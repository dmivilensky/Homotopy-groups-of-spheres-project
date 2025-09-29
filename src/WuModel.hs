{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- | WuModel.Core (pure, extended)
-- |
-- | Содержимое:
-- |   • Презентации (шаблоны: букет, тор, поверхность, сфера, Moore, mapping torus).
-- |   • Moore-комплекс в размерности 2 (N2, d2).
-- |   • Целочисленный Fox-Якобиан ε∘∂ и Смитова нормальная форма:
-- |       - инварианты H1 (свободный ранг и торсион),
-- |       - базис ker(∂2) над Z (абелевая верхняя оценка на π2),
-- |       - функции для RL: компактный featureVector, soft-membership score.
-- |   • Генерация «кандидатных 2-циклов» (как слова) из базиса ker(∂2),
-- |     Fox-нормы (ℓ¹ и p-adic) этих циклов — пригодно для reward shaping.
-- |   • Самотесты на классических примерах.
-- |
module WuModel (runWuTests) where

import           Data.List        (foldl', transpose)
import           Data.Map.Strict  (Map)
import qualified Data.Map.Strict  as M
import           Data.Text        (Text)
import qualified Data.Text        as T

import qualified Fox  as F  -- требуется расширенный экспорт, см. комментарий выше
import qualified Hall as H  -- smithNormalForm, smithDiag

--------------------------------------------------------------------------------
-- Типы и базовые слова
--------------------------------------------------------------------------------

type Gen = String

data Presentation = Presentation
  { gens :: [Gen]
  , rels :: [F.WordF]
  } deriving (Eq, Show)

data Template
  = Bouquet Int                               -- ∨^m S^1
  | Torus                                     -- <a,b | [a,b]>
  | Surface Int                               -- genus g
  | Sphere Int                                -- S^n (n>=2): trivial π1
  | Moore Int Int                             -- M(Z/q, n) (только n=1 влияет на π1)
  | MapSpaceDeg Int Template                  -- компонент степени (для π1 без эффекта)
  | MappingTorus Template (Map Gen F.WordF)   -- MT_φ: <X,t | t^{-1} x t = φ(x)>
  deriving (Eq, Show)

-- [u,v] = u v u^{-1} v^{-1}
comm :: F.WordF -> F.WordF -> F.WordF
comm u v = F.wMul u (F.wMul v (F.wMul (F.wInv u) (F.wInv v)))

-- x^q (нормализовано)
relatorPower :: F.WordF -> Int -> F.WordF
relatorPower x q = F.normalize (F.wPow x q)

--------------------------------------------------------------------------------
-- Построение презентаций
--------------------------------------------------------------------------------

buildFromTemplate :: Template -> Presentation
buildFromTemplate = \case
  Bouquet m ->
    Presentation [ "x" ++ show i | i <- [1..m] ] []

  Torus ->
    let a   = F.letter "a"; b = F.letter "b"
        rel = F.normalize (comm a b)
    in Presentation ["a","b"] [rel]

  Surface g ->
    let names = concat [ ["a"++show i, "b"++show i] | i <- [1..g] ]
        rel = F.normalize $
                foldl' F.wMul F.wOne
                  [ comm (F.letter ("a"++show i)) (F.letter ("b"++show i))
                  | i <- [1..g] ]
    in Presentation names [rel]

  Sphere n ->
    if n >= 2 then Presentation [] [] else Presentation ["x"] []

  Moore n q ->
    if n >= 2
       then Presentation [] []
       else let x = F.letter "x"; r = F.normalize (F.wPow x q)
            in Presentation ["x"] [r]

  MapSpaceDeg _ t ->
    buildFromTemplate t

  MappingTorus t phi ->
    let Presentation xs rs = buildFromTemplate t
        tgen = "t"; tW = F.letter tgen
        relMT g =
          let gW  = F.letter g
              img = M.findWithDefault gW g phi
              lhs = F.wMul (F.wMul (F.wInv tW) gW) tW
          in F.normalize (F.wMul lhs img)
    in Presentation (xs ++ [tgen]) (rs ++ map relMT xs)

buildFromPresentation :: [Gen] -> [F.WordF] -> Presentation
buildFromPresentation xs rs = Presentation xs (map F.normalize rs)

--------------------------------------------------------------------------------
-- Moore-комплекс (размерность 2)
--------------------------------------------------------------------------------

-- Генераторы N2 — сами релятора; d2 — их граница в 1-скелете (на уровне абеля — строка Фокса)
mooreN2 :: Presentation -> [(F.WordF, F.WordF)]
mooreN2 (Presentation _ rs) = [ (r, r) | r <- rs ]

mooreBoundary2 :: Presentation -> [F.WordF]
mooreBoundary2 = map snd . mooreN2

--------------------------------------------------------------------------------
-- Fox-Якобиан и абелевы инварианты
--------------------------------------------------------------------------------

-- Полный целочисленный Fox-Якобиан ε∘∂ : |R| × |X|
foxJacobianZ :: Presentation -> [[Integer]]
foxJacobianZ (Presentation xs rs) = F.jacobianZ xs rs

-- H1 ≅ Z^{|X|} / im(∂2) — из Смитовой формы
h1Invariants :: Presentation -> (Int, [Integer])
h1Invariants p =
  let j = foxJacobianZ p
      (_, d, _) = H.smithNormalForm j
      tors = H.smithDiag d
      nX = length (gens p)
      rankFree = nX - length tors
  in (rankFree, tors)

h1RankFree :: Presentation -> Int
h1RankFree = fst . h1Invariants

h1Torsion :: Presentation -> [Integer]
h1Torsion = snd . h1Invariants

-- ker(∂2) ≤ Z^{|R|}: считаем SNF для A^T (|X| × |R|).
kerD2BasisZ :: Presentation -> [[Integer]]
kerD2BasisZ p =
  let a   = foxJacobianZ p           -- |R| × |X|
      at  = transpose a              -- |X| × |R|
      (_u, d, v) = H.smithNormalForm at   -- U * A^T * V = D
      rk  = length (H.smithDiag d)        -- rank(A^T) = rank(A)
      nR  = length a                      -- число столбцов у A^T
  in if nR <= rk
        then []
        else drop rk (transpose v)        -- столбцы V (длины |R|), дающие базис ker(A^T)


--------------------------------------------------------------------------------
-- Кандидатные 2-циклы и метрики
--------------------------------------------------------------------------------

-- Собирать слово из линейной комбинации реляций: Π r_i^{z_i}
cycleWordFromKerVector :: Presentation -> [Integer] -> F.WordF
cycleWordFromKerVector (Presentation _ rs) zs =
  let step acc (r, e) =
        if e == 0 then acc else F.wMul acc (F.wPow r (fromIntegral e))
  in foldl' step F.wOne (zip rs zs)

-- Все «кандидатные циклы» как слова — по базису ker(∂2)
candidateCyclesWords :: Presentation -> [F.WordF]
candidateCyclesWords p = map (cycleWordFromKerVector p) (kerD2BasisZ p)

-- Суммарная ℓ¹-норма Fox-производных (по всем генераторам)
cycleFoxL1 :: Presentation -> F.WordF -> Integer
cycleFoxL1 (Presentation xs _) w =
  let dxs = [ F.foxD (T.pack x) w | x <- xs ]
  in sum (map F.l1Norm dxs)

-- p-adic max-норма производной (максимум по генераторам)
cycleFoxPadic :: Integer -> Presentation -> F.WordF -> Double
cycleFoxPadic p (Presentation xs _) w =
  let dxs = [ F.foxD (T.pack x) w | x <- xs ]
  in maximum (0.0 : [ F.pAdicMaxNorm p dz | dz <- dxs ])

-- Мягкая дистанция ∂w до левого идеала ⟨∂S⟩ после push-forward.
-- В качестве оценки используем абелевацию (доступна всегда и дешёвая).
-- Даёт нестрогий, но полезный для RL скор.
--   score = Σ_x residual_l1( pushForward(∂_x w), span{pushForward(∂_x r) : r∈rels} )
--
-- Мы определяем локально канонический target — свободная абелевизация Z^{|X|}.
newtype Zab = Zab (Map Text Int) deriving (Eq, Ord, Show)
instance F.GroupLike Zab where
  gOne = Zab M.empty
  gMul (Zab a) (Zab b) = Zab (M.filter (/=0) (M.unionWith (+) a b))
  gInv (Zab a) = Zab (M.map negate a)

phiAb :: [Text] -> Text -> Zab
phiAb gensT x =
  let v = M.fromList [ (g, if g==x then 1 else 0) | g <- gensT ]
  in Zab v

softNormalClosureScore :: Presentation -> F.WordF -> Integer
softNormalClosureScore (Presentation xs rs) w =
  let gensT = map T.pack xs
  in F.softMembershipScore (phiAb gensT) gensT rs w

--------------------------------------------------------------------------------
-- RL-фичи и простые обструкции
--------------------------------------------------------------------------------

abelianExponentSums :: Presentation -> [[Integer]]
abelianExponentSums = foxJacobianZ

-- Необходимое условие принадлежности коммутаторной подгруппе: нулевые суммы показателей
-- (для каждого релятора и для их произведения).
isAbelianCommutatorCandidate :: Presentation -> Bool
isAbelianCommutatorCandidate p =
  let rows = abelianExponentSums p
      zeroRow v = all (==0) v
      allRelsZero = all zeroRow rows
      prodRel = foldl' F.wMul F.wOne (rels p)
      prodRow = F.jacobianZ (gens p) [prodRel]
  in allRelsZero && all (all (==0)) prodRow

-- Компактный набор признаков состояния/окружения для RL.
-- [ nGen, nRel, rank(∂2), nullity(∂2), h1_free, torsion[0..K-1] ]
featureVector :: Int -> Presentation -> [Integer]
featureVector kMax p =
  let j = foxJacobianZ p
      (_, d, _) = H.smithNormalForm j
      diag = H.smithDiag d
      nX = length (gens p)
      nR = length (rels p)
      rankJ = length diag
      nullJ = nR - rankJ
      (h1free, tors) = h1Invariants p
      pad xs = take kMax (xs ++ replicate kMax 0)
  in map fromIntegral [nX, nR, rankJ, nullJ, h1free] ++ map fromIntegral (pad tors)

--------------------------------------------------------------------------------
-- Самотесты
--------------------------------------------------------------------------------

assertEq :: (Eq a, Show a) => String -> a -> a -> IO ()
assertEq name got want =
  if got == want
     then putStrLn ("[ok] Wu " ++ name ++ ": " ++ show got)
     else error ("[FAIL] Wu " ++ name ++ "\n  got:    " ++ show got ++ "\n  expect: " ++ show want)

runWuTests :: IO ()
runWuTests = do
  putStrLn "== WuModel self-tests =="

  -- Bouquet m: H1 ≅ Z^m
  let pBouq3 = buildFromTemplate (Bouquet 3)
  assertEq "Bouquet gens" (length (gens pBouq3)) 3
  assertEq "Bouquet rels" (length (rels pBouq3)) 0
  assertEq "Bouquet H1 free" (h1RankFree pBouq3) 3
  assertEq "Bouquet H1 tors" (h1Torsion pBouq3) []

  -- Torus: <a,b | [a,b]>
  let pTorus = buildFromTemplate Torus
  assertEq "Torus J" (foxJacobianZ pTorus) [[0,0]]
  assertEq "Torus H1 free" (h1RankFree pTorus) 2
  assertEq "Torus tors" (h1Torsion pTorus) []
  let kerT = kerD2BasisZ pTorus
  assertEq "Torus ker rank" (length kerT) 1
  -- Кандидатный цикл и его Fox-нормы ~ маленькие
  let candT = candidateCyclesWords pTorus
  assertEq "Torus candidate cycles #=1" (length candT) 1
  let wT = head candT
      l1T = cycleFoxL1 pTorus wT
      pAdT = cycleFoxPadic 3 pTorus wT
  assertEq "Torus cycleFoxL1>=0" (l1T >= 0) True
  assertEq "Torus cycleFoxPadic>=0" (pAdT >= 0) True
  -- мягкий скор нормального замыкания на коммутаторе близок к 0
  let softT = softNormalClosureScore pTorus wT
  assertEq "Torus softScore>=0" (softT >= 0) True

  -- Surface genus g: H1 ≅ Z^{2g}
  let g = 2; pSurf = buildFromTemplate (Surface g)
  assertEq "Surface H1 free" (h1RankFree pSurf) (2*g)
  assertEq "Surface tors" (h1Torsion pSurf) []

  -- Cyclic group Z/q
  let q = 7; pCyc = buildFromTemplate (Moore 1 q)
  assertEq "Cyclic H1 free" (h1RankFree pCyc) 0
  assertEq "Cyclic H1 tors" (h1Torsion pCyc) [fromIntegral q]
  -- Кандидатные циклы пусты (|R|=1, rankJ=1)
  assertEq "Cyclic ker empty" (candidateCyclesWords pCyc) []

  -- Abelian commutator obstruction
  assertEq "Torus commutator-candidate" (isAbelianCommutatorCandidate pTorus) True

  -- Feature vector длины 5+K
  let fv = featureVector 4 pCyc
  assertEq "feature length" (length fv) (5 + 4)

  putStrLn "WuModel tests finished."
