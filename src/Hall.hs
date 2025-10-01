{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

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
import           Data.List (intercalate, sortBy, foldl')
import           Data.Ord  (comparing)
import           GHC.Generics (Generic)
import           Control.DeepSeq (NFData(..))
import           Control.Parallel.Strategies
import           Data.Ratio (Rational, (%), numerator, denominator)

--------------------------------------------------------------------------------
-- Parallelism tuning (adjust for your machine/workload)
--------------------------------------------------------------------------------

parChunkPairs   :: Int ; parChunkPairs   = 64  -- for cartesian pairs in bracket
parChunkComps   :: Int ; parChunkComps   = 64  -- for BCH compositions
parChunkMaps    :: Int ; parChunkMaps    = 16  -- for merging per-chunk maps

-- Split a list into chunks of (at most) n elements.
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

-- Hall order: primary key is weight, then lexicographic on tree.
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

-- (u,v) is admissible if u > v and if u = [a,b] then b ≤ v.
{-# INLINE isHallPair #-}
isHallPair :: Basic -> Basic -> Bool
isHallPair u v =
  hallCompare u v == GT &&
  case u of
    Leaf _   -> True
    Node _ b -> hallCompare b v /= GT

genLeaves :: Int -> [Basic]
genLeaves k = [ Leaf (GenId i) | i <- [1..k] ]

-- Build Hall basis up to class c by increasing weight.
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
-- Lie over ℤ
--------------------------------------------------------------------------------

-- NOTE: Public representation kept as Map Basic … to preserve API.
newtype LieZ = LieZ { unLZ :: Map Basic Integer } deriving (Eq, Show, Generic, NFData)

zeroLZ :: LieZ
zeroLZ = LieZ M.empty

{-# INLINE singletonLZ #-}
singletonLZ :: Basic -> Integer -> LieZ
singletonLZ b c = if c == 0 then zeroLZ else LieZ (M.singleton b c)

{-# INLINE addLZ #-}
addLZ :: LieZ -> LieZ -> LieZ
addLZ (LieZ a) (LieZ b) = LieZ $ M.filter (/=0) $ M.unionWith (+) a b

{-# INLINE negLZ #-}
negLZ :: LieZ -> LieZ
negLZ (LieZ a) = LieZ (M.map negate a)

{-# INLINE scaleLZ #-}
scaleLZ :: Integer -> LieZ -> LieZ
scaleLZ s (LieZ a)
  | s == 0    = zeroLZ
  | s == 1    = LieZ a
  | otherwise = LieZ (M.filter (/=0) (M.map (s*) a))

-- Merge many maps once (batch) instead of chaining unions.
{-# INLINE plusManyLZ #-}
plusManyLZ :: [LieZ] -> LieZ
plusManyLZ zs =
  let pairs = concatMap (M.toList . unLZ) zs
  in LieZ $ M.filter (/=0) $ M.fromListWith (+) pairs

ppLieZ :: LieZ -> String
ppLieZ (LieZ m)
  | M.null m  = "0"
  | otherwise =
      intercalate " + "
        [ (if c==1 then "" else show c ++ "*") ++ ppBasic b
        | (b,c) <- M.toAscList m
        ]

-- Core Hall reduction on basis nodes:
--   For u>v:
--     admissible (u,v)  → [u,v] is a new basic node
--     otherwise (u=[a,b]) → [[a,b],v] = [a,[b,v]] + [[a,v],b]
{-# INLINE brBasicZ #-}
brBasicZ :: Int -> Basic -> Basic -> LieZ
brBasicZ c u v
  | weight u + weight v > c = zeroLZ
  | hallCompare u v == EQ   = zeroLZ
  | hallCompare u v == GT =
      if isHallPair u v
        then singletonLZ (Node u v) 1
        else case u of
               Leaf _ -> error "brBasicZ: Leaf>v but not admissible"
               Node a b ->
                 let !t1 = bracketLZ c (singletonLZ a 1) (brBasicZ c b v)
                     !t2 = bracketLZ c (brBasicZ c a v) (singletonLZ b 1)
                 in addLZ t1 t2
  | otherwise = negLZ (brBasicZ c v u)

{-# INLINE reduceBasic #-}
reduceBasic :: Int -> Basic -> Basic
reduceBasic c b = if weight b <= c then b else error "reduceBasic: overweight"

-- Efficient bracket over ℤ:
--   • produce contributions per cartesian pair in parallel;
--   • build per-chunk maps once (fromListWith), then fold a small list of maps.
{-# INLINE bracketLZ #-}
bracketLZ :: Int -> LieZ -> LieZ -> LieZ
bracketLZ _ (LieZ a) (LieZ b) | M.null a || M.null b = zeroLZ
bracketLZ c (LieZ a) (LieZ b) =
  let pairs = [ (u,ca,v,cb) | (u,ca) <- M.toList a, (v,cb) <- M.toList b ]
      mkChunk :: [(Basic,Integer,Basic,Integer)] -> LieZ
      mkChunk ps =
        let contribs =
              concat
                [ let !coef = ca * cb
                      !lz   = unLZ (brBasicZ c u v)
                  in [ (w, coef * k) | (w,k) <- M.toList lz ]
                | (u,ca,v,cb) <- ps
                ]
        in LieZ $ M.filter (/=0) $ M.fromListWith (+) contribs
      maps =
        ( map mkChunk (chunksOf parChunkPairs pairs)
          `using` parList rdeepseq )
  in foldl' addLZ zeroLZ maps

leafZ :: Int -> LieZ
leafZ i = singletonLZ (Leaf (GenId i)) 1

--------------------------------------------------------------------------------
-- Lie over ℚ + BCH
--------------------------------------------------------------------------------

newtype LieQ = LieQ { unLQ :: Map Basic Rational } deriving (Eq, Show, Generic, NFData)

zeroLQ :: LieQ
zeroLQ = LieQ M.empty

{-# INLINE singletonLQ #-}
singletonLQ :: Basic -> Rational -> LieQ
singletonLQ b c = if c == 0 then zeroLQ else LieQ (M.singleton b c)

{-# INLINE addLQ #-}
addLQ :: LieQ -> LieQ -> LieQ
addLQ (LieQ a) (LieQ b) = LieQ $ M.filter (/=0) $ M.unionWith (+) a b

{-# INLINE negLQ #-}
negLQ :: LieQ -> LieQ
negLQ (LieQ a) = LieQ (M.map negate a)

{-# INLINE scaleLQ #-}
scaleLQ :: Rational -> LieQ -> LieQ
scaleLQ s (LieQ a)
  | s == 0    = zeroLQ
  | s == 1    = LieQ a
  | otherwise = LieQ (M.filter (/=0) (M.map (s*) a))

-- Batch aggregation over ℚ.
{-# INLINE plusManyLQ #-}
plusManyLQ :: [LieQ] -> LieQ
plusManyLQ zs =
  let pairs = concatMap (M.toList . unLQ) zs
  in LieQ $ M.filter (/=0) $ M.fromListWith (+) pairs

ppLieQ :: LieQ -> String
ppLieQ (LieQ m)
  | M.null m  = "0"
  | otherwise =
      intercalate " + "
        [ (if r==1 then "" else show (numerator r) ++ "/" ++ show (denominator r) ++ "*")
          ++ ppBasic b
        | (b,r) <- M.toAscList m
        ]

{-# INLINE brBasicQ #-}
brBasicQ :: Int -> Basic -> Basic -> LieQ
brBasicQ c u v = LieQ (M.map fromInteger (unLZ (brBasicZ c u v)))

-- Efficient bracket over ℚ with chunked parallelism and batch aggregation.
{-# INLINE bracketLQ #-}
bracketLQ :: Int -> LieQ -> LieQ -> LieQ
bracketLQ c (LieQ a) (LieQ b)
  | M.null a || M.null b = zeroLQ
  | otherwise =
      let pairs = [ (u,ca,v,cb) | (u,ca) <- M.toList a, (v,cb) <- M.toList b ]
          mkChunk :: [(Basic,Rational,Basic,Rational)] -> LieQ
          mkChunk ps =
            let contribs =
                  concat
                    [ let !coef = ca * cb
                          !lz   = unLQ (brBasicQ c u v)
                      in [ (w, coef * k) | (w,k) <- M.toList lz ]
                    | (u,ca,v,cb) <- ps
                    ]
            in LieQ $ M.filter (/=0) $ M.fromListWith (+) contribs
          maps =
            ( map mkChunk (chunksOf parChunkPairs pairs)
              `using` parList rdeepseq )
      in foldl' addLQ zeroLQ maps

{-# INLINE toQ #-}
toQ :: LieZ -> LieQ
toQ (LieZ m) = LieQ (M.map fromInteger m)

{-# INLINE truncateByWeightQ #-}
truncateByWeightQ :: Int -> LieQ -> LieQ
truncateByWeightQ w (LieQ m) = LieQ (M.filterWithKey (\b _ -> weight b <= w) m)

-- Bernoulli via Akiyama–Tanigawa (B1 produced as +1/2) then flipped to B1=-1/2.
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

{-# INLINE fixB1 #-}
fixB1 :: [Rational] -> [Rational]
fixB1 (b0:b1:rest) = b0 : (-b1) : rest
fixB1 xs           = xs

-- ad-chain with early pruning: if any intermediate becomes zero, stop early.
{-# INLINE adChain #-}
adChain :: Int -> [LieQ] -> LieQ -> LieQ
adChain c ops v0 = go (reverse ops) v0
  where
    go []     !acc = acc
    go (u:us) !acc =
      let !acc' = bracketLQ c u acc
      in if M.null (unLQ acc') then zeroLQ else go us acc'

-- compositions of 'total' into exactly k positive parts (memoized by caller).
{-# INLINE compositionsK #-}
compositionsK :: Int -> Int -> [[Int]]
compositionsK total k
  | k <= 0          = []
  | k == 1          = if total >= 1 then [[total]] else []
  | otherwise       = [ i:rest
                      | i <- [1 .. total - (k-1)]
                      , rest <- compositionsK (total - i) (k-1)
                      ]

-- BCH up to class c:
--   Z = Σ_{n≥1} Z_n, deg(Z_n)=n
--   Z_1 = X + Y
--   Z_n = (1/n) Σ_{k=1}^{n-1} (B_k/k!) Σ_{i_1+…+i_k=n-1}
--            ad_{Z_{i_1}} … ad_{Z_{i_k}} (X + (-1)^k Y).
-- Parallelization:
--   • inner sums over compositions are mapped in parallel (chunked);
--   • per-k results are aggregated in batches before the outer fold.
bchQ :: Int -> LieQ -> LieQ -> LieQ
bchQ c x y
  | c <= 0    = zeroLQ
  | otherwise =
      let !bnums    = fixB1 (bernoullisAT (c-1))  -- B0..B_{c-1}
          !factList = scanl (*) 1 [1..]           -- 0!,1!,2!,…
          !z1       = addLQ x y

          -- Memo table for compositions reused across all n,k (saves a lot of list work).
          compMemo :: Map (Int,Int) [[Int]]
          compMemo =
            let keys  = [ (n-1,k) | n <- [2..c], k <- [1..n-1] ]
                items = [ ((t,k), compositionsK t k) | (t,k) <- keys ]
            in M.fromList items

          build :: Int -> [LieQ] -> [LieQ]
          build n acc
            | n > c     = []
            | otherwise =
                let ks = [1 .. n-1]

                    sumK :: LieQ
                    sumK =
                      let piecesPerK =
                            [ let bk    = bnums !! k
                                  kfacI = factList !! k
                                  coef  = bk / fromIntegral kfacI
                                  baseV = if odd k then addLQ x (negLQ y) else addLQ x y
                                  comps = M.findWithDefault [] (n-1,k) compMemo

                                  -- Evaluate ad-chains for all compositions in parallel,
                                  -- batch-aggregate into few maps, then scale by coef.
                                  part :: LieQ
                                  part =
                                    let perChunk =
                                          ( map (\chunk ->
                                                   plusManyLQ
                                                     [ adChain c (map (\r -> acc !! (r-1)) parts) baseV
                                                     | parts <- chunk
                                                     ])
                                                (chunksOf parChunkComps comps)
                                            `using` parList rdeepseq )
                                    in scaleLQ coef (plusManyLQ perChunk)
                              in part
                            | k <- ks
                            ]
                      in plusManyLQ piecesPerK

                    zn = scaleLQ (1 % fromIntegral n) sumK
                in zn : build (n+1) (acc ++ [zn])

          zs = z1 : build 2 [z1]
      in foldl' addLQ zeroLQ zs

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

insertLieZRight :: Int -> GroupNF -> LieZ -> GroupNF
insertLieZRight c nf (LieZ m)
  | M.null m  = nf
  | otherwise = M.foldlWithKey' (\acc b e -> insertManyRight c acc b e) nf m

-- [v,u^e] = Π_{k≥1} (ad_u^k v)^{binom(e,k)} (up to class c).
-- Uses the Lie bracket above; the pruning by class c keeps this bounded.
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
  | e > 0     = iter e nf
  | otherwise = groupInv (insertManyRight c (groupInv nf) b (-e))
  where
    iter 0 acc = acc
    iter m acc = iter (m-1) (insertOnceRight c acc b)

insertOnceRight :: Int -> GroupNF -> Basic -> GroupNF
insertOnceRight c (GroupNF xs0) b =
  let xs1   = xs0 ++ [(b,1)]
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
-- Smith Normal Form (integer)
--------------------------------------------------------------------------------

-- A small but impactful improvement: pick a pivot of minimal |a_ij|
-- in the remaining submatrix rather than “first non-zero”. This reduces
-- growth of intermediate values and number of Euclidean steps.
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

    -- Pick the position of the smallest non-zero entry by absolute value
    -- in the submatrix i.., j..
    pivotMinAbs :: Int -> Int -> [[Integer]] -> Maybe (Int,Int)
    pivotMinAbs i j a =
      let rs = [i .. nRows a - 1]
          cs = [j .. nCols a - 1]
          nz = [ (r,c,abs (a!!r!!c)) | r <- rs, c <- cs, a!!r!!c /= 0 ]
      in case nz of
           [] -> Nothing
           _  -> let (r,c,_) = minimumBy3 nz in Just (r,c)

    -- Extended gcd: s*a + t*b = g = gcd(a,b), g >= 0
    egcd :: Integer -> Integer -> (Integer, Integer, Integer)
    egcd a b = go (abs a) (abs b) 1 0 0 1
      where
        go r0 r1 s0 t0 s1 t1
          | r1 == 0  = (r0, signum a * s0, signum b * t0)
          | otherwise =
              let q  = r0 `quot` r1
              in go r1 (r0 - q*r1) s1 t1 (s0 - q*s1) (t0 - q*t1)

    -- 2×2 unimodular row-combo on rows i and r:
    --   [ s  t ] * [row_i] = new row_i,  a_ij -> g
    --   [-b' a']   [row_r] = new row_r,  a_rj -> 0
    -- where a' = a_ij/g, b' = a_rj/g.
    rowComb2 :: Int -> Int -> Integer -> Integer -> [[Integer]] -> [[Integer]]
             -> ([[Integer]], [[Integer]])
    rowComb2 i r aij arj a u =
      let (g,s,t) = egcd aij arj
          a' = aij `quot` g
          b' = arj `quot` g
          lin1 rowi rowr = zipWith (\x y -> s*x + t*y) rowi rowr
          lin2 rowi rowr = zipWith (\x y -> (-b')*x + a'*y) rowi rowr
          replaceRows m =
            let ri  = m!!i; rr  = m!!r
                ri' = lin1 ri rr
                rr' = lin2 ri rr
            in setRow r rr' (setRow i ri' m)
          a'new = replaceRows a
          u'new = replaceRows u
      in (u'new, a'new)

    -- 2×2 unimodular col-combo on cols j and c (via transposes).
    colComb2 :: Int -> Int -> Integer -> Integer -> [[Integer]] -> [[Integer]]
             -> ([[Integer]], [[Integer]])
    colComb2 j c aij aic a v =
      let (g,s,t) = egcd aij aic
          a' = aij `quot` g
          b' = aic `quot` g
          lin1 colj colc = zipWith (\x y -> s*x + t*y) colj colc
          lin2 colj colc = zipWith (\x y -> (-b')*x + a'*y) colj colc
          aT = transpose' a
          vT = transpose' v
          (vT', aT') =
            let cj  = aT!!j; cc  = aT!!c
                cj' = lin1 cj cc
                cc' = lin2 cj cc
                repl m = setRow c cc' (setRow j cj' m)
            in (repl vT, repl aT)
      in (transpose' vT', transpose' aT')

    -- Euclidean clear on (row i, col j).
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

    -- tiny matrix utilities
    nRows mtx = length mtx
    nCols mtx = if null mtx then 0 else length (head mtx)
    ident k = [ [ if r==c then 1 else 0 | c <- [0..k-1] ] | r <- [0..k-1] ]
    rowSwap r1 r2 mtx = swapBy r1 r2 mtx
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
-- Utilities & tests (kept identical in spirit to original)
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
