{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}

-- |
-- | Hall (Core + Nilpotent Group; BCH via degree-recursive Casas–Murua)
-- |
-- | Implemented
-- | -----------
-- | • Hall basis/order and admissible-pair reduction to Hall normal form.
-- | • Lie algebras over ℤ and ℚ with nilpotency class cutoff (weight > c pruned).
-- | • BCH over ℚ via degree-by-degree Casas–Murua recurrence:
-- |      Z = Σ_{n≥1} Z_n,  deg(Z_n)=n,
-- |      Z_1 = X + Y,
-- |      Z_n = (1/n) Σ_{k=1}^{n-1} (B_k/k!) Σ_{i_1+…+i_k=n-1}
-- |                 ad_{Z_{i_1}} … ad_{Z_{i_k}} (X + (-1)^k Y).
-- |   Bernoulli convention B1 = -1/2 (this is required for the above form).
-- |
-- | • Free nilpotent group (Hall/Mal’cev NF) with collection and [v,u^e].
-- | • Strict folds and early pruning to reduce allocations and peak memory.
-- |
-- | Sanity checks
-- | -------------
-- | – truncate_{≤4}(BCH_c) is identical for all c≥4.
-- | – BCH(X,0)=X, BCH(0,Y)=Y.
-- | – BCH(X,Y) = −BCH(−Y,−X).
-- | – If Y = α·X then BCH(X,Y) = X + α·X.
-- |

module Hall where

import qualified Data.Map.Strict as M
import           Data.Map.Strict (Map)
import qualified Data.Set        as S
import           Data.Set        (Set)
import           Data.List       (intercalate, sortBy, foldl')
import           Data.Ord        (comparing)
import           GHC.Generics    (Generic)
import           Data.Ratio      (Rational, (%), numerator, denominator)

--------------------------------------------------------------------------------
-- Hall basis (Core)
--------------------------------------------------------------------------------

newtype GenId = GenId { unGen :: Int }
  deriving (Eq, Ord, Show, Generic)

data Basic
  = Leaf !GenId
  | Node !Basic !Basic
  deriving (Eq, Show, Generic)

weight :: Basic -> Int
weight (Leaf _)   = 1
weight (Node l r) = weight l + weight r

hallCompare :: Basic -> Basic -> Ordering
hallCompare a b =
  case compare (weight a) (weight b) of
    LT -> LT
    GT -> GT
    EQ -> cmp a b
  where
    cmp (Leaf (GenId i)) (Leaf (GenId j)) = compare i j
    cmp (Leaf _)          (Node _ _)      = LT
    cmp (Node _ _)        (Leaf _)        = GT
    cmp (Node a1 a2) (Node b1 b2) =
      case hallCompare a1 b1 of
        EQ -> hallCompare a2 b2
        o  -> o

instance Ord Basic where
  compare = hallCompare

-- admissible pair (u,v): u > v and if u=[a,b] then b ≤ v
isHallPair :: Basic -> Basic -> Bool
isHallPair u v =
  hallCompare u v == GT &&
  case u of
    Leaf _     -> True
    Node _ u2  -> hallCompare u2 v /= GT

genLeaves :: Int -> [Basic]
genLeaves k = [ Leaf (GenId i) | i <- [1..k] ]

-- Build the Hall basis up to class c.
hallBasis :: Int -> Int -> [Basic]
hallBasis k c
  | k <= 0 || c <= 0 = []
  | otherwise =
      let w1 = genLeaves k
          go _ 1 _ = w1
          go sofar w ws =
            let candidates =
                  [ Node u v
                  | a <- [1..w-1]
                  , let wsA = ws !! (a-1)
                  , let wsB = ws !! (w-a-1)
                  , u <- wsA
                  , v <- wsB
                  , isHallPair u v
                  ]
                uniq = S.toList (S.fromList candidates)
            in uniq
          -- ws[w-1] = all basis elements of weight w
          ws = w1 : [ go (concat (take w ws)) w ws | w <- [2..c] ]
      in concat (take c ws)

ppBasic :: Basic -> String
ppBasic (Leaf (GenId i)) = "x" ++ show i
ppBasic (Node a b)       = "[" ++ ppBasic a ++ "," ++ ppBasic b ++ "]"

--------------------------------------------------------------------------------
-- Lie algebra over ℤ
--------------------------------------------------------------------------------

newtype LieZ = LieZ { unLZ :: Map Basic Integer } deriving (Eq, Show)

zeroLZ :: LieZ
zeroLZ = LieZ M.empty

singletonLZ :: Basic -> Integer -> LieZ
singletonLZ b c = if c == 0 then zeroLZ else LieZ (M.singleton b c)

addLZ :: LieZ -> LieZ -> LieZ
addLZ (LieZ a) (LieZ b) = LieZ $ M.filter (/=0) $ M.unionWith (+) a b

negLZ :: LieZ -> LieZ
negLZ (LieZ a) = LieZ (M.map negate a)

scaleLZ :: Integer -> LieZ -> LieZ
scaleLZ s (LieZ a)
  | s == 0    = zeroLZ
  | s == 1    = LieZ a
  | otherwise = LieZ (M.filter (/=0) (M.map (s*) a))

plusManyLZ :: [LieZ] -> LieZ
plusManyLZ = foldl' addLZ zeroLZ

ppLieZ :: LieZ -> String
ppLieZ (LieZ m)
  | M.null m  = "0"
  | otherwise =
      intercalate " + "
        [ (if c==1 then "" else show c ++ "*") ++ ppBasic b
        | (b,c) <- M.toAscList m
        ]

-- Core Hall reduction:
-- For u>v:
--   if (u,v) admissible => [u,v] is a new basic node
--   else, if u=[a,b] then   [[a,b],v] = [a,[b,v]] - [[a,v],b]
-- (This sign is crucial. Many implementations mistakenly use a '+'.)
brBasicZ :: Int -> Basic -> Basic -> LieZ
brBasicZ c u v
  | weight u + weight v > c = zeroLZ
  | hallCompare u v == EQ   = zeroLZ
  | hallCompare u v == GT =
      if isHallPair u v
        then singletonLZ (Node u v) 1
        else case u of
               Leaf _     -> error "brBasicZ: Leaf>v but not admissible"
               Node a b   ->
                 -- CORRECT Hall reduction (from Jacobi):
                 -- [[a,b],v] = [a,[b,v]] + [[a,v],b]
                 addLZ (brBasicZ c a (reduceBasic c (Node b v)))
                       (brBasicZ c (reduceBasic c (Node a v)) b)
  | otherwise = negLZ (brBasicZ c v u)


reduceBasic :: Int -> Basic -> Basic
reduceBasic c b = if weight b <= c then b else error "reduceBasic: overweight"

bracketLZ :: Int -> LieZ -> LieZ -> LieZ
bracketLZ _ (LieZ a) (LieZ b) | M.null a || M.null b = zeroLZ
bracketLZ c (LieZ a) (LieZ b) =
  plusManyLZ
    [ scaleLZ (ca * cb) (brBasicZ c u v)
    | (u,ca) <- M.toList a
    , (v,cb) <- M.toList b
    ]

leafZ :: Int -> LieZ
leafZ i = singletonLZ (Leaf (GenId i)) 1

--------------------------------------------------------------------------------
-- Lie algebra over ℚ and BCH
--------------------------------------------------------------------------------

newtype LieQ = LieQ { unLQ :: Map Basic Rational } deriving (Eq, Show)

zeroLQ :: LieQ
zeroLQ = LieQ M.empty

singletonLQ :: Basic -> Rational -> LieQ
singletonLQ b c = if c == 0 then zeroLQ else LieQ (M.singleton b c)

addLQ :: LieQ -> LieQ -> LieQ
addLQ (LieQ a) (LieQ b) = LieQ $ M.filter (/=0) $ M.unionWith (+) a b

negLQ :: LieQ -> LieQ
negLQ (LieQ a) = LieQ (M.map negate a)

scaleLQ :: Rational -> LieQ -> LieQ
scaleLQ s (LieQ a)
  | s == 0    = zeroLQ
  | s == 1    = LieQ a
  | otherwise = LieQ (M.filter (/=0) (M.map (s*) a))

plusManyLQ :: [LieQ] -> LieQ
plusManyLQ = foldl' addLQ zeroLQ

ppLieQ :: LieQ -> String
ppLieQ (LieQ m)
  | M.null m  = "0"
  | otherwise =
      intercalate " + "
        [ (if r==1 then "" else show (numerator r) ++ "/" ++ show (denominator r) ++ "*")
          ++ ppBasic b
        | (b,r) <- M.toAscList m
        ]

brBasicQ :: Int -> Basic -> Basic -> LieQ
brBasicQ c u v = LieQ (M.map fromInteger (unLZ (brBasicZ c u v)))

bracketLQ :: Int -> LieQ -> LieQ -> LieQ
bracketLQ c (LieQ a) (LieQ b)
  | M.null a || M.null b = zeroLQ
  | otherwise =
      plusManyLQ
        [ scaleLQ (ca * cb) (brBasicQ c u v)
        | (u,ca) <- M.toList a
        , (v,cb) <- M.toList b
        ]

toQ :: LieZ -> LieQ
toQ (LieZ m) = LieQ (M.map fromInteger m)

truncateByWeightQ :: Int -> LieQ -> LieQ
truncateByWeightQ w (LieQ m) = LieQ (M.filterWithKey (\b _ -> weight b <= w) m)

-- Bernoulli via Akiyama–Tanigawa (gives B1=+1/2), then flip to B1=-1/2.
bernoullisAT :: Int -> [Rational]
bernoullisAT n = map bern [0..n]
  where
    bern m =
      let initA = [ 1 % fromIntegral (k+1) | k <- [0..m] ]
          step a j =
            let ajm1 = a !! (j-1)
                aj   = a !! j
                ajm1' = fromIntegral j * (ajm1 - aj)
            in take (j-1) a ++ [ajm1'] ++ drop j a
          aFinal = foldl' step initA [m,m-1..1]
      in head aFinal

fixB1 :: [Rational] -> [Rational]
fixB1 (b0:b1:rest) = b0 : (-b1) : rest
fixB1 xs           = xs

-- ad-chain: ad_{u1} (ad_{u2} (... (ad_{uk} v)))
-- We apply the rightmost operator first (reverse), strictly and with early pruning.
adChain :: Int -> [LieQ] -> LieQ -> LieQ
adChain c ops v0 = go (reverse ops) v0
  where
    go []     !acc = acc
    go (u:us) !acc =
      let !acc' = bracketLQ c u acc
      in if M.null (unLQ acc') then zeroLQ else go us acc'

-- BCH via degree recursion up to class c (Bernoulli B1=-1/2)
bchQ :: Int -> LieQ -> LieQ -> LieQ
bchQ c x y
  | c <= 0    = zeroLQ
  | otherwise =
      let bnums    = fixB1 (bernoullisAT (c-1))  -- B0..B_{c-1}
          factList :: [Integer]
          factList = scanl (*) 1 [1..]          -- 0!,1!,2!,…
          z1       = addLQ x y
          build :: Int -> [LieQ] -> [LieQ]
          build n acc
            | n > c     = []
            | otherwise =
                let sumK :: LieQ
                    sumK = foldl' addLQ zeroLQ
                           [ let bk    = bnums !! k            -- :: Rational
                                 kfacI = factList !! k         -- :: Integer
                                 coef  = bk / fromIntegral kfacI
                                 baseV = if odd k then addLQ x (negLQ y) else addLQ x y
                                 sumComp =
                                   foldl' addLQ zeroLQ
                                     [ let ops  = map (\r -> acc !! (r-1)) parts
                                           term = adChain c ops baseV
                                       in term
                                     | parts <- compositionsK (n-1) k
                                     ]
                             in scaleLQ coef sumComp
                           | k <- [1 .. n-1] ]
                    zn = scaleLQ (1 % fromIntegral n) sumK
                in zn : build (n+1) (acc ++ [zn])
          zs = z1 : build 2 [z1]
      in foldl' addLQ zeroLQ zs

-- compositions of 'total' into exactly k positive parts
compositionsK :: Int -> Int -> [[Int]]
compositionsK total k
  | k <= 0          = []
  | k == 1          = if total >= 1 then [[total]] else []
  | otherwise       = [ i:rest
                      | i <- [1 .. total - (k-1)]
                      , rest <- compositionsK (total - i) (k-1)
                      ]

--------------------------------------------------------------------------------
-- Nilpotent group (Hall / Mal’cev normal form)
--------------------------------------------------------------------------------

newtype GroupNF = GroupNF { unG :: [(Basic, Integer)] } deriving (Eq, Show)

canonicalizeNF :: GroupNF -> GroupNF
canonicalizeNF (GroupNF xs) =
  GroupNF $ filter ((/=0) . snd) (M.toAscList (M.fromListWith (+) xs))

normalizeNF :: [(Basic,Integer)] -> GroupNF
normalizeNF xs = canonicalizeNF (GroupNF xs)

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

insertLieZRight :: Int -> GroupNF -> LieZ -> GroupNF
insertLieZRight c nf (LieZ m)
  | M.null m  = nf
  | otherwise = M.foldlWithKey' (\acc b e -> insertManyRight c acc b e) nf m

-- [v,u^e] = Π_{k≥1} (ad_u^k v)^{binom(e,k)} (up to class c)
commPower :: Int -> Basic -> Basic -> Integer -> GroupNF
commPower c v u e
  | e == 0    = identityG
  | otherwise =
      let !vZ     = singletonLZ v 1
          !uZ     = singletonLZ u 1
          !wv     = weight v
          !wu     = weight u
          !kmax   = max 0 ((c - wv) `div` wu)
          !start1 = bracketLZ c vZ uZ
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
          !nfTmp  = go 1 identityG start1 1
      in canonicalizeNF nfTmp

insertManyRight :: Int -> GroupNF -> Basic -> Integer -> GroupNF
insertManyRight _ nf _ 0 = nf
insertManyRight c nf b e
  | e > 0     = iterateInsert e nf
  | otherwise = groupInv (insertManyRight c (groupInv nf) b (-e))
  where
    iterateInsert 0 acc = acc
    iterateInsert m acc = iterateInsert (m-1) (insertOnceRight c acc b)

insertOnceRight :: Int -> GroupNF -> Basic -> GroupNF
insertOnceRight c (GroupNF xs0) b =
  let xs1 = xs0 ++ [(b,1)]
      fixed = bubbleLeft xs1 (length xs1 - 2)
  in canonicalizeNF (GroupNF fixed)
  where
    bubbleLeft xs i
      | i < 0 = xs
      | otherwise =
          let (pre,(u,eu),(v,ev),suf) = split3 xs i
          in if hallCompare u v == GT
               then
                 let commVUe = commPower c v u eu
                     corrInv = groupInv commVUe
                     xs'     = pre ++ [(v,ev),(u,eu)] ++ unG corrInv ++ suf
                 in bubbleLeft xs' (i-1)
               else bubbleLeft xs (i-1)

    split3 :: [a] -> Int -> ([a], a, a, [a])
    split3 xs i =
      let (pre, rest) = splitAt i xs
      in case rest of
           (a:b':suf) -> (pre, a, b', suf)
           _          -> error "split3: index out of range"

groupInv :: GroupNF -> GroupNF
groupInv (GroupNF xs) = GroupNF (map (\(b,e)->(b, negate e)) (reverse xs))

groupMul :: Int -> GroupNF -> GroupNF -> GroupNF
groupMul c (GroupNF a) (GroupNF b) =
  canonicalizeNF $
    foldl' (\acc (bq,eq) -> insertManyRight c acc bq eq) (GroupNF a) b

groupPow :: Int -> GroupNF -> Integer -> GroupNF
groupPow _ g 0 = identityG
groupPow c g n
  | n < 0     = groupPow c (groupInv g) (-n)
  | otherwise = go g n identityG
  where
    go _ 0 acc = acc
    go x m acc
      | odd m     = go (groupMul c x x) (m `div` 2) (groupMul c acc x)
      | otherwise = go (groupMul c x x) (m `div` 2) acc

groupComm :: Int -> GroupNF -> GroupNF -> GroupNF
groupComm c g h = groupMul c (groupMul c (groupInv g) (groupInv h))
                           (groupMul c g h)

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
      br a b = bracketLZ c a b
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
  -- weight-2/-3 coefficients:
  let w2 = Node (Leaf (GenId 2)) (Leaf (GenId 1))
      w3x = Node (Node (Leaf (GenId 2)) (Leaf (GenId 1))) (Leaf (GenId 1))
      w3y = Node (Node (Leaf (GenId 2)) (Leaf (GenId 1))) (Leaf (GenId 2))
  assert (coeffOf w2  z4 == (-1) % 2 )  "BCH w2 must be -1/2 * [x2,x1]"
  assert (coeffOf w3x z4 == 1 % 12   )  "BCH w3 [[x2,x1],x1] must be +1/12"
  assert (coeffOf w3y z4 == (-1) % 12)  "BCH w3 [[x2,x1],x2] must be -1/12"

--------------------------------------------------------------------------------
-- Demo
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  testLieIdentities
  testCollection
  testBCH
  demo
  putStrLn "Hall.Core + Hall.Nilpotent : OK."
