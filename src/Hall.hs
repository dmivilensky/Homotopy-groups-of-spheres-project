{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE TupleSections #-}

-- |
-- | Hall basis / order and reduction to Hall normal form for free Lie algebras.
-- | Lie algebras over ℤ and ℚ with class cutoff (nodes with weight > c are pruned).
-- | BCH over ℚ via Casas–Murua degree-by-degree recurrence with Bernoulli B1 = -1/2.
-- | Free nilpotent group (Hall/Mal’cev NF) with collection and power-commutators.
-- |
-- | Performance techniques integrated:
-- | • Strict evaluation everywhere (bang patterns, strict fields);
-- | • Parallel map/reduce with Strategies, tuned chunking;
-- | • Batch aggregation: build few large maps once, not many tiny ones;
-- | • Composition tables memoized once per BCH call;
-- | • Symmetry-aware bracket and early “weight” pruning where cheap;
-- | • Better pivot selection in Smith Normal Form to reduce coefficient blow-up.
-- |
-- | Public API and behaviour preserved; built-in tests pass unchanged.
-- |

module Hall
  ( Basic(..), GenId(..)
  , LieZ(..), LieQ(..), negLQ, zeroLQ, singletonLQ
  , ppGroupNF, insertLieZRight, addLQ, scaleLQ, bracketLQ, toQ
  , truncateByWeightQ, bchQ, weight
  , GroupNF(..), identityG, groupMul, groupPow, groupComm, normalizeNF, lieZtoG
  , smithNormalForm, smithDiag
  , runHallTests
  ) where

import qualified Data.Map.Strict as M
import           Data.Map.Strict (Map)
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import           Data.List (intercalate, sortBy, foldl')
import           Data.Ord  (comparing)
import           GHC.Generics (Generic)
import           Control.DeepSeq (NFData(..))
import           Control.Parallel.Strategies
import           Data.Ratio (Rational, (%), numerator, denominator)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import           Data.Bifunctor (second)

--------------------------------------------------------------------------------
-- Parallelism tuning
--------------------------------------------------------------------------------

parChunkPairs   :: Int ; parChunkPairs   = 64
parChunkComps   :: Int ; parChunkComps   = 64

chunksOf :: Int -> [a] -> [[a]]
chunksOf n xs | n <= 0    = [xs]
              | otherwise = go xs
  where
    go [] = []
    go ys = let (a,b) = splitAt n ys in a : go b

--------------------------------------------------------------------------------
-- Hall basis
--------------------------------------------------------------------------------

newtype GenId = GenId { unGen :: Int }
  deriving (Eq, Ord, Show, Generic, NFData)

data Basic
  = Leaf !GenId
  | Node !Basic !Basic
  deriving (Eq, Show, Generic, NFData)

{-# INLINE weight #-}
weight :: Basic -> Int
weight (Leaf _)   = 1
weight (Node l r) = weight l + weight r

-- Hall compare by (weight, lex)
hallCompare :: Basic -> Basic -> Ordering
hallCompare a b =
  case compare (weight a) (weight b) of
    LT -> LT
    GT -> GT
    EQ ->
      case (a,b) of
        (Leaf (GenId i), Leaf (GenId j)) -> compare i j
        (Leaf _,          Node _ _     ) -> LT
        (Node _ _,        Leaf _       ) -> GT
        (Node a1 a2,     Node b1 b2    ) ->
          case hallCompare a1 b1 of
            EQ -> hallCompare a2 b2
            o  -> o
instance Ord Basic where compare = hallCompare

{-# INLINE isHallPair #-}
isHallPair :: Basic -> Basic -> Bool
isHallPair u v =
  hallCompare u v == GT &&
  case u of
    Leaf _   -> True
    Node _ b -> hallCompare b v /= GT

genLeaves :: Int -> [Basic]
genLeaves k = [ Leaf (GenId i) | i <- [1..k] ]

-- Build Hall basis up to class c
hallBasis :: Int -> Int -> [Basic]
hallBasis k c
  | k <= 0 || c <= 0 = []
  | otherwise =
      let w1 = genLeaves k
          go !_ 1 _  = w1
          go !_ w ws =
            let wsA a = ws !! (a-1)
                candidates =
                  [ Node u v
                  | a <- [1..w-1]
                  , u <- wsA a
                  , v <- wsA (w-a)
                  , isHallPair u v
                  ]
                uniq = S.toList (S.fromList candidates)
            in uniq
          ws = w1 : [ go (concat (take w ws)) w ws | w <- [2..c] ]
      in concat (take c ws)

ppBasic :: Basic -> String
ppBasic (Leaf (GenId i)) = "x" ++ show i
ppBasic (Node a b)       = "[" ++ ppBasic a ++ "," ++ ppBasic b ++ "]"

--------------------------------------------------------------------------------
-- Public Lie over ℤ / ℚ (внешнее API как было)
--------------------------------------------------------------------------------

newtype LieZ = LieZ { unLZ :: Map Basic Integer } deriving (Eq, Show, Generic, NFData)
newtype LieQ = LieQ { unLQ :: Map Basic Rational } deriving (Eq, Show, Generic, NFData)

-- Публичные smart-конструкторы (нужны многим местам ниже)
{-# INLINE singletonLZ #-}
singletonLZ :: Basic -> Integer -> LieZ
singletonLZ b c =
  if c == 0 then LieZ M.empty else LieZ (M.singleton b c)

{-# INLINE singletonLQ #-}
singletonLQ :: Basic -> Rational -> LieQ
singletonLQ b r =
  if r == 0 then LieQ M.empty else LieQ (M.singleton b r)


{-# INLINE addLQ #-}
addLQ :: LieQ -> LieQ -> LieQ
addLQ (LieQ a) (LieQ b) = LieQ $ M.filter (/=0) $ M.unionWith (+) a b

{-# INLINE addLZ #-}
addLZ :: LieZ -> LieZ -> LieZ
addLZ (LieZ a) (LieZ b) = LieZ $ M.filter (/=0) $ M.unionWith (+) a b

{-# INLINE negLQ #-}
negLQ :: LieQ -> LieQ
negLQ (LieQ a) = LieQ (M.map negate a)

{-# INLINE negLZ #-}
negLZ :: LieZ -> LieZ
negLZ (LieZ a) = LieZ (M.map negate a)

zeroLQ :: LieQ
zeroLQ = LieQ M.empty

zeroLZ :: LieZ
zeroLZ = LieZ M.empty

{-# INLINE scaleLZ #-}
scaleLZ :: Integer -> LieZ -> LieZ
scaleLZ s (LieZ a)
  | s == 0    = zeroLZ
  | s == 1    = LieZ a
  | otherwise = LieZ (M.filter (/=0) (M.map (s*) a))
{-# INLINE scaleLQ #-}
scaleLQ :: Rational -> LieQ -> LieQ
scaleLQ s (LieQ a)
  | s == 0    = zeroLQ
  | s == 1    = LieQ a
  | otherwise = LieQ (M.filter (/=0) (M.map (s*) a))

ppLieQ :: LieQ -> String
ppLieQ (LieQ m)
  | M.null m  = "0"
  | otherwise =
      intercalate " + "
        [ (if r==1 then "" else show (numerator r) ++ "/" ++ show (denominator r) ++ "*")
          ++ ppBasic b
        | (b,r) <- M.toAscList m
        ]
ppLieZ :: LieZ -> String
ppLieZ (LieZ m)
  | M.null m  = "0"
  | otherwise =
      intercalate " + "
        [ (if c==1 then "" else show c ++ "*") ++ ppBasic b
        | (b,c) <- M.toAscList m
        ]

{-# INLINE toQ #-}
toQ :: LieZ -> LieQ
toQ (LieZ m) = LieQ (M.map fromInteger m)

{-# INLINE truncateByWeightQ #-}
truncateByWeightQ :: Int -> LieQ -> LieQ
truncateByWeightQ w (LieQ m) = LieQ (M.filterWithKey (\b _ -> weight b <= w) m)

--------------------------------------------------------------------------------
-- BasisEnv: внутренние ID, веса и быстрые карты
--------------------------------------------------------------------------------

data BasisEnv = BasisEnv
  { beNodeOf   :: !(Int -> Basic)        -- id -> Basic
  , beIdOf     :: !(Basic -> Int)        -- Basic -> id
  , beWeightV  :: !(U.Vector Int)        -- weight per id
  }

-- Построить окружение для заданного k (макс. генератор) и класса c
buildEnv :: Int -> Int -> BasisEnv
buildEnv k c =
  let basis = hallBasis k c
      n     = length basis
      nodeV = V.fromList basis
      wV    = U.generate n (\i -> weight (nodeV V.! i))
      idMap = M.fromList (zip basis [0..])
      beId x = M.findWithDefault (error "beIdOf: unknown node") x idMap
      beNode i | i >= 0 && i < n = nodeV V.! i
               | otherwise       = error "beNodeOf: bad id"
  in BasisEnv { beNodeOf = beNode, beIdOf = beId, beWeightV = wV }

-- Определить k (максимальный номер генератора) из терма
maxGenInBasic :: Basic -> Int
maxGenInBasic = \case
  Leaf (GenId i) -> i
  Node a b       -> max (maxGenInBasic a) (maxGenInBasic b)

maxGenInMap :: Map Basic t -> Int
maxGenInMap m = foldl' (\acc b -> max acc (maxGenInBasic b)) 1 (M.keys m)

--------------------------------------------------------------------------------
-- Локальное мемо для разложения [u,v] в базис (в ID-пространстве)
--------------------------------------------------------------------------------

type LZ' = IM.IntMap Integer
type LQ' = IM.IntMap Rational

-- уникальные пары (сохраним порядок u>v/иное в brBasic*)
uniquePairs :: (Ord a, Ord b) => [(a,b)] -> [(a,b)]
uniquePairs xs = M.keys (M.fromList (map (, ()) xs))

-- базовый расчёт через старое brBasicZ на Basic, затем конверт в ID-вектор
brBasicZ_BASIC :: Int -> Basic -> Basic -> LieZ
brBasicZ_BASIC c u v
  | weight u + weight v > c = zeroLZ
  | hallCompare u v == EQ   = zeroLZ
  | hallCompare u v == GT =
      if isHallPair u v
        then singletonLZ (Node u v) 1
        else case u of
               Leaf _ -> error "brBasicZ: Leaf>v but not admissible"
               Node a b ->
                 let t1 = bracketLZ c (singletonLZ a 1) (brBasicZ_BASIC c b v)
                     t2 = bracketLZ c (brBasicZ_BASIC c a v) (singletonLZ b 1)
                 in addLZ t1 t2
  | otherwise = negLZ (brBasicZ_BASIC c v u)

-- Построить кэш для набора пар на ID: (i,j) -> IntMap (id -> coef)
buildBrMemoIdZ :: BasisEnv -> Int -> [(Int,Int)] -> M.Map (Int,Int) LZ'
buildBrMemoIdZ be c pairs =
  let toIdMap (LieZ m) =
        IM.fromListWith (+)
          [ (beIdOf be b, coef) | (b,coef) <- M.toList m, coef /= 0 ]
      mk (i,j) =
        let u = beNodeOf be i; v = beNodeOf be j
        in ((i,j), toIdMap (brBasicZ_BASIC c u v))
      chunks = chunksOf parChunkPairs pairs
      parts =
        ( map (M.fromList . map mk) chunks
          `using` parList rdeepseq )
  in foldl' (M.unionWith const) M.empty parts

--------------------------------------------------------------------------------
-- Конвертация между публичным и внутренним представлением
--------------------------------------------------------------------------------

toIntMapZ :: BasisEnv -> LieZ -> LZ'
toIntMapZ be (LieZ m) =
  IM.fromListWith (+) [ (beIdOf be b, c) | (b,c) <- M.toList m, c /= 0 ]

toIntMapQ :: BasisEnv -> LieQ -> LQ'
toIntMapQ be (LieQ m) =
  IM.fromListWith (+) [ (beIdOf be b, r) | (b,r) <- M.toList m, r /= 0 ]

fromIntMapZ :: BasisEnv -> LZ' -> LieZ
fromIntMapZ be im =
  LieZ $ M.fromList
      [ (beNodeOf be i, c) | (i,c) <- IM.toList im, c /= 0 ]
fromIntMapQ :: BasisEnv -> LQ' -> LieQ
fromIntMapQ be im =
  LieQ $ M.fromList
      [ (beNodeOf be i, r) | (i,r) <- IM.toList im, r /= 0 ]

plusManyIMZ :: [LZ'] -> LZ'
plusManyIMZ zs = IM.fromListWith (+) (concatMap IM.toList zs)
plusManyIMQ :: [LQ'] -> LQ'
plusManyIMQ zs = IM.fromListWith (+) (concatMap IM.toList zs)

--------------------------------------------------------------------------------
-- Внутренние скобки на ID с локальным кэшем
--------------------------------------------------------------------------------

-- Публичная: скобка над ℤ, используя внутренний движок.
{-# INLINE bracketLZ #-}
bracketLZ :: Int -> LieZ -> LieZ -> LieZ
bracketLZ c aZ bZ
  | M.null (unLZ aZ) || M.null (unLZ bZ) = zeroLZ
  | otherwise =
      let k = max (maxGenInMap (unLZ aZ)) (maxGenInMap (unLZ bZ))
          be = buildEnv k c
          aI = toIntMapZ be aZ
          bI = toIntMapZ be bZ
          al = IM.toList aI
          bl = IM.toList bI
          pairsIJ = uniquePairs [ (i,j) | (i,_) <- al, (j,_) <- bl ]
          memo   = buildBrMemoIdZ be c pairsIJ

          mkChunk :: [(Int,Integer,Int,Integer)] -> LZ'
          mkChunk ps =
            let contribs =
                  concat
                    [ let !coef = ca * cb
                      in if coef == 0
                           then []
                           else
                             case M.lookup (i,j) memo of
                               Nothing   -> []
                               Just term -> [ (w, coef * k) | (w,k) <- IM.toList term, k /= 0 ]
                    | (i,ca,j,cb) <- ps
                    ]
            in IM.fromListWith (+) contribs

          cart = [ (i,ca,j,cb) | (i,ca) <- al, (j,cb) <- bl ]
          parts =
            ( map mkChunk (chunksOf parChunkPairs cart)
              `using` parList rdeepseq )
      in fromIntMapZ be (plusManyIMZ parts)

-- Публичная: скобка над ℚ через тот же кэш (цель — не дублировать разложения).
{-# INLINE bracketLQ #-}
bracketLQ :: Int -> LieQ -> LieQ -> LieQ
bracketLQ c aQ bQ
  | M.null (unLQ aQ) || M.null (unLQ bQ) = zeroLQ
  | otherwise =
      let k = max (maxGenInMap (M.map (const ()) (unLQ aQ)))
                  (maxGenInMap (M.map (const ()) (unLQ bQ)))
          be = buildEnv k c
          aI = toIntMapQ be aQ
          bI = toIntMapQ be bQ
          al = IM.toList aI
          bl = IM.toList bI
          pairsIJ = uniquePairs [ (i,j) | (i,_) <- al, (j,_) <- bl ]
          memo   = buildBrMemoIdZ be c pairsIJ

          mkChunk :: [(Int,Rational,Int,Rational)] -> LQ'
          mkChunk ps =
            let contribs =
                  concat
                    [ let !coef = ca * cb
                      in if coef == 0
                           then []
                           else
                             case M.lookup (i,j) memo of
                               Nothing   -> []
                               Just term ->
                                 [ (w, coef * fromInteger k0)
                                 | (w,k0) <- IM.toList term, k0 /= 0
                                 ]
                    | (i,ca,j,cb) <- ps
                    ]
            in IM.fromListWith (+) contribs

          cart = [ (i,ca,j,cb) | (i,ca) <- al, (j,cb) <- bl ]
          parts =
            ( map mkChunk (chunksOf parChunkPairs cart)
              `using` parList rdeepseq )
      in fromIntMapQ be (plusManyIMQ parts)

--------------------------------------------------------------------------------
-- BCH (Casas–Murua) на ℚ с внутренним представлением
--------------------------------------------------------------------------------

-- Bernoulli via Akiyama–Tanigawa (B1 produced as +1/2) then flipped to -1/2.
bernoullisAT :: Int -> [Rational]
bernoullisAT n = map bern [0..n]
  where
    bern m =
      let initA = [ 1 % fromIntegral (k+1) | k <- [0..m] ]
          step a j =
            let ajm1  = a !! (j-1)
                aj    = a !! j
                ajm1' = fromIntegral j * (ajm1 - aj)
            in take (j-1) a ++ [ajm1'] ++ drop j a
          aFinal = foldl' step initA [m,m-1..1]
      in head aFinal
fixB1 :: [Rational] -> [Rational]
fixB1 (b0:b1:rest) = b0 : (-b1) : rest
fixB1 xs           = xs

-- ad-chain (внутренний, на ID)
adChainI :: Int -> BasisEnv -> [LQ'] -> LQ' -> LQ'
adChainI c be ops = go (reverse ops)
  where
    go []     !acc = acc
    go (u:us) !acc =
      let !acc' = bracketI c be u acc
      in if IM.null acc' then IM.empty else go us acc'
    -- скобка для внутренних представлений (без пересборки LieQ)
    bracketI :: Int -> BasisEnv -> LQ' -> LQ' -> LQ'
    bracketI cc be' l r
      | IM.null l || IM.null r = IM.empty
      | otherwise =
          toIntMapQ be' ( bracketLQ cc (fromIntMapQ be' l) (fromIntMapQ be' r) )

-- compositions of 'total' into exactly k positive parts
compositionsK :: Int -> Int -> [[Int]]
compositionsK total k
  | k <= 0    = []
  | k == 1    = [[total] | total >= 1]
  | otherwise = [ i:rest
                | i <- [1 .. total - (k-1)]
                , rest <- compositionsK (total - i) (k-1)
                ]

bchQ :: Int -> LieQ -> LieQ -> LieQ
bchQ c x0 y0
  | c <= 0    = zeroLQ
  | otherwise =
      let k = max (maxGenInMap (M.map (const ()) (unLQ x0)))
                  (maxGenInMap (M.map (const ()) (unLQ y0)))
          be = buildEnv k c
          xI = toIntMapQ be x0
          yI = toIntMapQ be y0
          bnums    = fixB1 (bernoullisAT (c-1))     -- B0..B_{c-1}
          factList = scanl (*) 1 [1..] :: [Int]     -- 0!,1!,2!,…
          z1I      = IM.unionWith (+) xI yI

          -- memo композиций
          compMemo :: M.Map (Int,Int) [[Int]]
          compMemo =
            let keys  = [ (n-1,k') | n <- [2..c], k' <- [1..n-1] ]
                items = [ ((t,k'), compositionsK t k') | (t,k') <- keys ]
            in M.fromList items

          build :: Int -> [LQ'] -> [LQ']
          build n acc
            | n > c     = []
            | otherwise =
                let ks = [1 .. n-1]
                    sumK :: LQ'
                    sumK =
                      let piecesPerK =
                            [ let bk    = bnums !! k'
                                  kfacI = factList !! k'
                                  coef  = bk / fromIntegral kfacI
                                  baseV = if odd k' then IM.unionWith (+) xI (IM.map negate yI)
                                                     else IM.unionWith (+) xI yI
                                  comps = M.findWithDefault [] (n-1,k') compMemo
                                  part  =
                                    let perChunk =
                                          ( map (\chunk ->
                                                   plusManyIMQ
                                                     [ adChainI c be (map (\r -> acc !! (r-1)) parts) baseV
                                                     | parts <- chunk
                                                     ])
                                                (chunksOf parChunkComps comps)
                                            `using` parList rdeepseq )
                                    in IM.map (* coef) (plusManyIMQ perChunk)
                              in part
                            | k' <- ks
                            ]
                      in plusManyIMQ piecesPerK
                    zn = IM.map (* (1 % fromIntegral n)) sumK
                in zn : build (n+1) (acc ++ [zn])

          zsI = z1I : build 2 [z1I]
      in fromIntMapQ be (plusManyIMQ zsI)

--------------------------------------------------------------------------------
-- Nilpotent group (Hall / Mal’cev NF)
--------------------------------------------------------------------------------

newtype GroupNF = GroupNF { unG :: [(Basic, Integer)] } deriving (Eq, Show, Generic, NFData)

canonicalizeNF :: GroupNF -> GroupNF
canonicalizeNF (GroupNF xs) =
  GroupNF $ filter ((/=0) . snd) (M.toAscList (M.fromListWith (+) xs))

normalizeNF :: [(Basic,Integer)] -> GroupNF
normalizeNF = canonicalizeNF . GroupNF

identityG :: GroupNF
identityG = GroupNF []

lieZtoG :: LieZ -> GroupNF
lieZtoG (LieZ m) = GroupNF $ M.toAscList m

ppGroupNF :: GroupNF -> String
ppGroupNF (GroupNF xs)
  | null xs   = "1"
  | otherwise =
      intercalate " * "
        [ case e of
            1 -> ppBasic b
            _ -> ppBasic b ++ "^" ++ show e
        | (b,e) <- xs
        ]

{-# INLINE binom #-}
binom :: Integer -> Integer -> Integer
binom n k
  | k < 0 || k > n   = 0
  | k == 0 || k == n = 1
  | otherwise =
      let k' = min k (n-k)
      in foldl' (\acc i -> (acc * (n - i + 1)) `div` i) 1 [1..k']

leafZ :: Int -> LieZ
leafZ i = singletonLZ (Leaf (GenId i)) 1

insertLieZRight :: Int -> GroupNF -> LieZ -> GroupNF
insertLieZRight c nf (LieZ m)
  | M.null m  = nf
  | otherwise = M.foldlWithKey' (insertManyRight c) nf m

-- [v,u^e] = Π_{k≥1} (ad_u^k v)^{binom(e,k)} (до класса c).
commPower :: Int -> Basic -> Basic -> Integer -> GroupNF
commPower c v u e
  | e == 0    = identityG
  | otherwise =
      let vZ     = singletonLZ v 1
          uZ     = singletonLZ u 1
          wv     = weight v
          wu     = weight u
          kmax   = max 0 ((c - wv) `div` wu)
          start1 = bracketLZ c vZ uZ
          go :: Int -> GroupNF -> LieZ -> Integer -> GroupNF
          go !k !accNF !curr !chooseEK
            | k > kmax           = accNF
            | M.null (unLZ curr) = accNF
            | otherwise =
                let !kI        = toInteger k
                    !kIm1      = toInteger (k - 1)
                    !chooseEK' = (chooseEK * (e - kIm1)) `div` kI
                    !accNF'    = insertLieZRight c accNF (scaleLZ chooseEK' curr)
                    !next      = bracketLZ c curr uZ
                in go (k+1) accNF' next chooseEK'
          nfTmp  = go 1 identityG start1 1
      in canonicalizeNF nfTmp

insertManyRight :: Int -> GroupNF -> Basic -> Integer -> GroupNF
insertManyRight _ nf _ 0 = nf
insertManyRight c nf b e
  | e > 0     = iter e nf
  | otherwise = groupInv (insertManyRight c (groupInv nf) b (-e))
  where
    iter 0 acc = acc
    iter m acc = iter (m-1) (insertOnceRight c acc b)

-- Переписанный «пузырёк» через разностные списки (без splitAt/многих ++).
insertOnceRight :: Int -> GroupNF -> Basic -> GroupNF
insertOnceRight c (GroupNF xs0) b =
  let xs1 = xs0 ++ [(b,1)]  -- единственный неизбежный ++ на добавление справа
      -- go проходит слева направо, двигая вставленный элемент влево при необходимости.
      go :: ([(Basic,Integer)] -> [(Basic,Integer)])  -- dlist для префикса
         -> [(Basic,Integer)]                         -- текущий остаток
         -> GroupNF
      go pre lst =
        case lst of
          -- минимум два элемента, чтобы потенциально свапнуть
          (u,eu):(v,ev):suf
            | hallCompare u v == GT ->
                -- нужно поменять местами u и v и добавить коррекцию
                let commVUe = commPower c v u eu
                    corrInv = groupInv commVUe
                    -- собираем новую «фронтовую» часть без аллокаций хвостов
                    newFront = pre . (\xs -> (v,ev) : (u,eu) : xs) . (unG corrInv ++)
                in go newFront suf
            | otherwise ->
                -- порядок нормальный, «зафиксировать» u и двигаться дальше
                go (pre . ((u,eu):)) ((v,ev):suf)
          -- остался один элемент — дописываем и каноникализуем
          [x] -> canonicalizeNF (GroupNF (pre [x]))
          -- пусто — уже собрали всё
          []  -> canonicalizeNF (GroupNF (pre []))
  in go id xs1

groupInv :: GroupNF -> GroupNF
groupInv (GroupNF xs) = GroupNF (map (second negate) (reverse xs))

groupMul :: Int -> GroupNF -> GroupNF -> GroupNF
groupMul c (GroupNF a) (GroupNF b) =
  canonicalizeNF $
    foldl' (\acc (bq,eq) -> insertManyRight c acc bq eq) (GroupNF a) b

groupPow :: Int -> GroupNF -> Integer -> GroupNF
groupPow _ g 0 = identityG
groupPow c g n
  | n < 0     = groupPow c (groupInv g) (-n)
  | otherwise = pow g n identityG
  where
    pow _ 0 acc = acc
    pow x m acc
      | odd m     = pow (groupMul c x x) (m `div` 2) (groupMul c acc x)
      | otherwise = pow (groupMul c x x) (m `div` 2) acc

groupComm :: Int -> GroupNF -> GroupNF -> GroupNF
groupComm c g h = groupMul c (groupMul c (groupInv g) (groupInv h))
                           (groupMul c g h)

--------------------------------------------------------------------------------
-- Smith Normal Form (минимизация роста коэффициентов — выбор малого пивота)
--------------------------------------------------------------------------------

smithNormalForm :: [[Integer]] -> ([[Integer]], [[Integer]], [[Integer]])
smithNormalForm a0 =
  let m  = length a0
      n  = if null a0 then 0 else length (head a0)
      u0 = ident m
      v0 = ident n
  in go 0 0 u0 a0 v0
  where
    go i j u a v
      | i >= nRows a || j >= nCols a = (u, a, v)
      | otherwise =
          case pivotMinAbs i j a of
            Nothing     -> (u, a, v)
            Just (r, c) ->
              let u1 = rowSwap i r u
                  a1 = rowSwap i r a
                  v1 = colSwap j c v
                  a2 = colSwap j c a1
              in if a2!!i!!j == 0
                    then go i (j+1) u1 a2 v1
                    else
                      let (u3, a3, v3) = clear i j u1 a2 v1
                      in go (i+1) (j+1) u3 a3 v3

    pivotMinAbs :: Int -> Int -> [[Integer]] -> Maybe (Int,Int)
    pivotMinAbs i j a =
      let rs = [i .. nRows a - 1]
          cs = [j .. nCols a - 1]
          nz = [ (r,c,abs (a!!r!!c)) | r <- rs, c <- cs, a!!r!!c /= 0 ]
      in case nz of
           [] -> Nothing
           _  -> let (r,c,_) = minimumBy3 nz in Just (r,c)

    egcd :: Integer -> Integer -> (Integer, Integer, Integer)
    egcd a b = go (abs a) (abs b) 1 0 0 1
      where
        go r0 r1 s0 t0 s1 t1
          | r1 == 0  = (r0, signum a * s0, signum b * t0)
          | otherwise =
              let q  = r0 `quot` r1
              in go r1 (r0 - q*r1) s1 t1 (s0 - q*s1) (t0 - q*t1)

    rowComb2 :: Int -> Int -> Integer -> Integer -> [[Integer]] -> [[Integer]]
             -> ([[Integer]], [[Integer]])
    rowComb2 i r aij arj a u =
      let (g,s,t) = egcd aij arj
          a' = aij `quot` g
          b' = arj `quot` g
          lin1 = zipWith (\x y -> s*x + t*y)
          lin2 = zipWith (\x y -> (-b')*x + a'*y)
          replaceRows m =
            let ri  = m!!i; rr  = m!!r
                ri' = lin1 ri rr
                rr' = lin2 ri rr
            in setRow r rr' (setRow i ri' m)
          a'new = replaceRows a
          u'new = replaceRows u
      in (u'new, a'new)

    colComb2 :: Int -> Int -> Integer -> Integer -> [[Integer]] -> [[Integer]]
             -> ([[Integer]], [[Integer]])
    colComb2 j c aij aic a v =
      let (g,s,t) = egcd aij aic
          a' = aij `quot` g
          b' = aic `quot` g
          lin1 = zipWith (\x y -> s*x + t*y)
          lin2 = zipWith (\x y -> (-b')*x + a'*y)
          aT = transpose' a
          vT = transpose' v
          (vT', aT') =
            let cj  = aT!!j; cc  = aT!!c
                cj' = lin1 cj cc
                cc' = lin2 cj cc
                repl m = setRow c cc' (setRow j cj' m)
            in (repl vT, repl aT)
      in (transpose' vT', transpose' aT')

    clear i j u a v =
      let fixSign (uM,aM) =
            if aM!!i!!j < 0
              then (negRow i uM, setAt2 i j (-(aM!!i!!j)) (negRow i aM))
              else (uM,aM)

          colLoop uM aM =
            case [ r | r <- [0..nRows aM - 1], r /= i, aM!!r!!j /= 0 ] of
              []     -> (uM, aM)
              (r:_)  ->
                let (u1,a1) = rowComb2 i r (aM!!i!!j) (aM!!r!!j) aM uM
                in colLoop u1 a1

          rowLoop aM vM =
            case [ c | c <- [0..nCols aM - 1], c /= j, aM!!i!!c /= 0 ] of
              []     -> (aM, vM)
              (c:_)  ->
                let (v1,a1) = colComb2 j c (aM!!i!!j) (aM!!i!!c) aM vM
                in rowLoop a1 v1

          (u1,a1)   = colLoop u a
          (a2,v1)   = rowLoop a1 v
          (u2,a3)   = fixSign (u1,a2)
      in (u2, a3, v1)

    nRows = length
    nCols mtx = if null mtx then 0 else length (head mtx)
    ident k = [ [ if r==c then 1 else 0 | c <- [0..k-1] ] | r <- [0..k-1] ]
    rowSwap = swapBy
    colSwap c1 c2 mtx = transpose' (swapBy c1 c2 (transpose' mtx))
    negRow r mtx = setRow r (map negate (mtx!!r)) mtx
    setRow r new mtx = [ if i==r then new else mtx!!i | i <- [0..nRows mtx - 1] ]
    setAt2 i j x mtx = setRow i (setAt j x (mtx!!i)) mtx
    setAt j x row    = [ if k==j then x else row!!k | k <- [0..length row - 1] ]
    swapBy i j xs    = [ xs!!perm k | k <- [0..length xs - 1] ]
      where perm k | k==i = j | k==j = i | otherwise = k
    transpose' []         = []
    transpose' ([]   : _) = []
    transpose' rows       = map head rows : transpose' (map tail rows)
    minimumBy3 ((r,c,v):rest) = go (r,c,v) rest
      where
        go acc [] = let (i,j,_) = acc in (i,j,())
        go acc ((r',c',v'):xs)
          | v' < (\(_,_,t)->t) acc = go (r',c',v') xs
          | otherwise              = go acc xs
    minimumBy3 [] = error "minimumBy3: empty"

smithDiag :: [[Integer]] -> [Integer]
smithDiag d =
  let r = length d
      c = if null d then 0 else length (head d)
      k = min r c
  in [ d!!i!!i | i <- [0..k-1], d!!i!!i /= 0 ]

--------------------------------------------------------------------------------
-- Utilities & tests
--------------------------------------------------------------------------------

dimByWeight :: Int -> Int -> [(Int, Int)]
dimByWeight k c =
  let allB = hallBasis k c
      groups = M.toList $ M.fromListWith (+) [ (weight b, 1::Int) | b <- allB ]
  in sortBy (comparing fst) groups

assert :: Bool -> String -> IO ()
assert True  _   = pure ()
assert False msg = error ("Assertion failed: " ++ msg)

coeffOf :: Basic -> LieQ -> Rational
coeffOf b (LieQ m) = M.findWithDefault 0 b m

testLieIdentities :: IO ()
testLieIdentities = do
  let c  = 6
      x1 = leafZ 1
      x2 = leafZ 2
      x3 = leafZ 3
      br = bracketLZ c
      zero   = zeroLZ
      anti a b = assert (addLZ (br a b) (br b a) == zero) "antisym failed"
      jac a b d =
        let lhs = addLZ (br a (br b d))
                $ addLZ (br b (br d a))
                        (br d (br a b))
        in assert (lhs == zero) "Jacobi failed"
  anti x1 x2
  anti x1 x3
  anti x2 x3
  jac x1 x2 x3

testCollection :: IO ()
testCollection = do
  let c = 6
      x1g = GroupNF [(Leaf (GenId 1),1)]
      x2g = GroupNF [(Leaf (GenId 2),1)]
      prod = groupMul c x2g x1g
      comm = commPower c (Leaf (GenId 1)) (Leaf (GenId 2)) 1
      expected = groupMul c (GroupNF [(Leaf (GenId 1),1),(Leaf (GenId 2),1)]) (groupInv comm)
  assert (prod == expected) "collection x2*x1 failed"

testBCH :: IO ()
testBCH = do
  let gen i = toQ (leafZ i)
      x = gen 1
      y = gen 2
  let z4 = bchQ 4 x y
      z5 = bchQ 5 x y
      z6 = bchQ 6 x y
  putStrLn "\n[BCH debug]"
  putStrLn $ "  c=4: " ++ ppLieQ z4
  putStrLn $ "  c=5: " ++ ppLieQ z5
  putStrLn $ "  c=6: " ++ ppLieQ z6
  putStrLn $ "  trunc4(c=5)-z4: " ++ ppLieQ (addLQ (truncateByWeightQ 4 z5) (negLQ z4))
  putStrLn $ "  trunc4(c=6)-z4: " ++ ppLieQ (addLQ (truncateByWeightQ 4 z6) (negLQ z4))
  assert (truncateByWeightQ 4 z5 == z4) "BCH: c=5 disagrees up to weight 4"
  assert (truncateByWeightQ 4 z6 == z4) "BCH: c=6 disagrees up to weight 4"
  -- key coefficients:
  let w2  = Node (Leaf (GenId 2)) (Leaf (GenId 1))
      w3x = Node (Node (Leaf (GenId 2)) (Leaf (GenId 1))) (Leaf (GenId 1))
      w3y = Node (Node (Leaf (GenId 2)) (Leaf (GenId 1))) (Leaf (GenId 2))
  assert (coeffOf w2  z4 == (-1) % 2 )  "BCH w2 must be -1/2 * [x2,x1]"
  assert (coeffOf w3x z4 == 1 % 12   )  "BCH w3 [[x2,x1],x1] must be +1/12"
  assert (coeffOf w3y z4 == (-1) % 12)  "BCH w3 [[x2,x1],x2] must be -1/12"

ppGroup :: GroupNF -> String
ppGroup = ppGroupNF

demo :: IO ()
demo = do
  putStrLn "== Hall / Nilpotent group demo (BCH by degree recursion) =="
  let k = 3
      c = 6
  putStrLn $ "k="++show k++", class c="++show c
  putStrLn $ "By weight: " ++ show (dimByWeight k c)
  let x1 = GroupNF [(Leaf (GenId 1),1)]
      x2 = GroupNF [(Leaf (GenId 2),1)]
      x3 = GroupNF [(Leaf (GenId 3),1)]
      g  = groupMul c x2 x1
      h  = groupMul c (groupMul c x3 x2) x1
      gh = groupMul c g h
      comm = groupComm c h g
  putStrLn $ "g   = x2 * x1 -> " ++ ppGroup g
  putStrLn $ "h   = x3 * x2 * x1 -> " ++ ppGroup h
  putStrLn $ "g*h = " ++ ppGroup gh
  putStrLn $ "[h,g] = " ++ ppGroup comm
  putStrLn ""
  let x1q = toQ (leafZ 1)
      x2q = toQ (leafZ 2)
  mapM_ (\cc -> do
           let z = bchQ cc x1q x2q
           putStrLn $ "BCH(log x1, log x2), class " ++ show cc ++ ":"
           putStrLn $ "  " ++ ppLieQ z
        ) [2..6]

runHallTests :: IO ()
runHallTests = do
  testLieIdentities
  testCollection
  testBCH
  demo
  putStrLn "Hall.Core + Hall.Nilpotent : OK."

  -- Smith Normal Form quick checks
  let a1 = [[6,10],[15,25]]
      (_, d1, _) = smithNormalForm a1
  assertEqHall "SNF diag a1 == [1]" (smithDiag d1) [1]

  let a2 = [[2,4],[6,8]]
      (_, d2, _) = smithNormalForm a2
  assertEqHall "SNF diag a2 == [2,4]" (smithDiag d2) [2,4]

  let a3 = replicate 2 (replicate 3 0)
      (_, d3, _) = smithNormalForm a3
  assertEqHall "SNF diag a3 == []" (smithDiag d3) []

  putStrLn "Hall tests finished."

assertEqHall :: (Eq a, Show a) => String -> a -> a -> IO ()
assertEqHall name got expect =
  if got == expect
     then putStrLn ("[ok] Hall " ++ name ++ ": " ++ show got)
     else error ("[FAIL] Hall " ++ name ++ "\n  got:    " ++ show got ++ "\n  expect: " ++ show expect)
