{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- Lambda algebra over F_p (odd p), parallel & vector-optimized
--  * Generators λ_i, μ_i (internal 0-based; printed 1-based)
--  * d^1 (deg -1), graded Leibniz
--  * Odd-prime Adem relations (LL/LM/ML/MM) → Curtis admissible NF
--  * Basis by degree (built once up to cap)
--  * Homology report using adaptive rank (now vectorized):
--      - column-wise Gaussian-like rank if rows ≤ cols
--      - row-wise (via transpose idea) if cols < rows
--  * Lucas binomial with per-prime cached factorials/invfactorials
--  * No unsafe (!!); vector ops for linear algebra
--  * Hot paths parallelized with Strategies (parMap rdeepseq)

module Lambda
  ( Prime(..), Gen(..), WordL(..)
  , toAdmissible, d1, degW, parseWord
  , reducePolyFull, buildBasisBundle
  , runLambdaTests
  , renderWord
  ) where

import qualified Data.Map.Strict as M
import           Data.Map.Strict (Map)
import qualified Data.Set        as S
import           Data.Set        (Set)
import           Data.List       (intercalate, sort)
import           Data.Char       (isDigit, toLower)
import           Data.Foldable   (foldl')
import           Control.DeepSeq (NFData(..))
import           Control.Parallel.Strategies (parMap, rdeepseq)
import           Control.Monad   (when)
import           Data.Maybe      (fromMaybe)

import qualified Data.Vector.Unboxed as U
import           Data.Vector.Unboxed (Vector)

import           Data.IORef
import           System.IO.Unsafe (unsafePerformIO)

--------------------------------------------------------------------------------
-- Coeffs over F_p
--------------------------------------------------------------------------------

newtype Prime = OddP { unP :: Int } deriving (Eq, Ord, Show)

modP :: Prime -> Int -> Int
modP (OddP p) !x = let r = x `mod` p in if r < 0 then r + p else r
{-# INLINE modP #-}

addP, subP, mulP :: Prime -> Int -> Int -> Int
addP pr a b = modP pr (a + b)
subP pr a b = modP pr (a - b)
mulP pr a b = modP pr (a * b)
{-# INLINE addP #-}
{-# INLINE subP #-}
{-# INLINE mulP #-}

powMod :: Int -> Int -> Int -> Int
powMod _ 0 m = 1 `mod` m
powMod a e m
  | even e = let t = powMod a (e `div` 2) m in (t*t) `mod` m
  | otherwise      = (a `mod` m) * powMod a (e-1) m `mod` m

invModPrime :: Prime -> Int -> Int
invModPrime pr@(OddP p) a = powMod (modP pr a) (p-2) p
{-# INLINE invModPrime #-}

--------------------------------------------------------------------------------
-- Safe indexing helpers (still used in word-level code; rank uses vectors)
--------------------------------------------------------------------------------

getAt :: [a] -> Int -> Maybe a
getAt xs i
  | i < 0     = Nothing
  | otherwise = go xs i
  where
    go [] _     = Nothing
    go (y:_)  0 = Just y
    go (_:ys) k = go ys (k-1)

getAtD :: a -> [a] -> Int -> a
getAtD def xs i = fromMaybe def (getAt xs i)

setAt :: Int -> a -> [a] -> [a]
setAt i a xs
  | i < 0     = xs
  | otherwise = go xs i
  where
    go [] _     = []
    go (_:ys) 0 = a : ys
    go (y:ys) k = y : go ys (k-1)

--------------------------------------------------------------------------------
-- Lambda.Core: gens/words/polys
--------------------------------------------------------------------------------

data Gen = Lam !Int | Mu !Int deriving (Eq, Ord)

-- NFData instances required for rdeepseq (parMap)
instance NFData Gen where
  rnf (Lam i) = rnf i
  rnf (Mu  i) = rnf i

instance Show Gen where
  show (Lam i) = "lambda" ++ show (i+1)
  show (Mu  i) = "mu"     ++ show (i+1)

newtype WordL = W { unW :: [Gen] } deriving (Eq, Ord)

instance NFData WordL where
  rnf (W gs) = rnf gs

instance Show WordL where
  show (W [])   = "1"
  show (W gens) = unwords (map show gens)

-- | Textual rendering compatible with 'parseWord'.
--   NOTE: Empty word renders to an empty line (""), not "1",
--   so that a round-trip (render -> parseWord) succeeds:
--     parseWord "" == Just (W [])
--     parseWord "lambda3 mu2" == Just (W [Lam 2, Mu 1])
renderWord :: WordL -> String
renderWord (W [])   = ""
renderWord (W gens) = unwords (map show gens)
{-# INLINE renderWord #-}

(><) :: WordL -> WordL -> WordL
W a >< W b = W (a ++ b)
infixl 7 ><

degGen :: Int -> Gen -> Int
degGen p (Lam i) = 2*(i+1)*(p-1) - 1
degGen p (Mu  i) = 2*(i+1)*(p-1)

degW :: Int -> WordL -> Int
degW p (W gs) = sum (map (degGen p) gs)

type Poly = Map WordL Int

normalizePoly :: Prime -> Poly -> Poly
normalizePoly pr = M.filter (/=0) . M.map (modP pr)
{-# INLINE normalizePoly #-}

zeroPoly :: Poly
zeroPoly = M.empty

mono :: Prime -> Int -> WordL -> Poly
mono pr c w = normalizePoly pr (M.singleton w c)
{-# INLINE mono #-}

addPoly :: Prime -> Poly -> Poly -> Poly
addPoly pr =
  M.mergeWithKey
    (\_ a b -> let c = addP pr a b in if c == 0 then Nothing else Just c)
    id id
{-# INLINE addPoly #-}

scalePoly :: Prime -> Int -> Poly -> Poly
scalePoly pr s
  | s' == 0   = const zeroPoly
  | s' == 1   = id
  | otherwise = normalizePoly pr . M.map (mulP pr s')
  where s' = modP pr s
{-# INLINE scalePoly #-}

mulLeftW :: Prime -> WordL -> Poly -> Poly
mulLeftW pr w poly =
  normalizePoly pr $ M.fromListWith (addP pr)
    [ (w >< w1, c) | (w1,c) <- M.toList poly ]
{-# INLINE mulLeftW #-}

mulRightW :: Prime -> Poly -> WordL -> Poly
mulRightW pr poly w =
  normalizePoly pr $ M.fromListWith (addP pr)
    [ (w1 >< w, c) | (w1,c) <- M.toList poly ]
{-# INLINE mulRightW #-}

--------------------------------------------------------------------------------
-- Lucas binomial with global cache per p
--------------------------------------------------------------------------------

-- Cache: p -> (facts[0..p-1], invfacts[0..p-1])
{-# NOINLINE lucasCacheRef #-}
lucasCacheRef :: IORef (Map Int ([Int],[Int]))
lucasCacheRef = unsafePerformIO (newIORef M.empty)

digitsBase :: Int -> Int -> [Int]
digitsBase p n
  | n <= 0    = [0]
  | otherwise = go n
  where
    go 0 = []
    go t = (t `mod` p) : go (t `div` p)

getLucasTables :: Int -> ([Int],[Int])
getLucasTables p = unsafePerformIO $ do
  m <- readIORef lucasCacheRef
  case M.lookup p m of
    Just v  -> pure v
    Nothing -> do
      let facts    = scanl (\a b -> (a*b) `mod` p) 1 [1..p-1]  -- facts !! 0 == 1
          inv x    = powMod x (p-2) p
          invfacts = 1 : map (inv . (facts !!)) [1..p-1]       -- invfacts !! 0 == 1
      let v = (facts, invfacts)
      writeIORef lucasCacheRef (M.insert p v m)
      pure v

smallChooseCached :: Int -> [Int] -> [Int] -> Int -> Int -> Int
smallChooseCached p facts invfacts n k
  | k < 0 || k > n = 0
  | otherwise      = (((facts !! n) * (invfacts !! k)) `mod` p) * (invfacts !! (n-k)) `mod` p
{-# INLINE smallChooseCached #-}

binomModP :: Int -> Int -> Int -> Int
binomModP p n k
  | k < 0 || k > n = 0
  | otherwise =
      let (facts, invfacts) = getLucasTables p
          dsN = digitsBase p n
          dsK = digitsBase p k
          f ni ki =
            if ki > ni then 0 else smallChooseCached p facts invfacts ni ki
      in foldl' (\acc (ni,ki) -> (acc * f ni ki) `mod` p) 1 (zip dsN (dsK ++ repeat 0))
{-# INLINE binomModP #-}

--------------------------------------------------------------------------------
-- d^1 (deg -1) + Leibniz
--------------------------------------------------------------------------------

d1Gen :: Prime -> WordL -> Poly
d1Gen pr@(OddP p) (W [Lam n]) =
  if n <= 0
    then zeroPoly
    else
      let terms =
            [ ( W [Lam i] >< W [Lam (n-1-i)], binomModP p (n+1) (i+1) )
            | i <- [0 .. n-1]
            ]
      in normalizePoly pr $ M.fromListWith (addP pr) terms
d1Gen pr@(OddP p) (W [Mu n]) =
  let terms = concat
        [ [ ( W [Lam i] >< W [Mu (n-i)] ,  binomModP p (n+1) (i+1) )
          , ( W [Mu  i] >< W [Lam (n-i)],  modP pr (negate (binomModP p (n+1) (i+1))) )
          ]
        | i <- [0 .. n]
        ]
  in normalizePoly pr $ M.fromListWith (addP pr) terms
d1Gen _ _ = zeroPoly
{-# INLINE d1Gen #-}

d1 :: Prime -> WordL -> Poly
d1 pr@(OddP p) (W [])     = zeroPoly
d1 pr           (W [g])   = d1Gen pr (W [g])
d1 pr@(OddP p)  (W (g:gs)) =
  let u   = W [g]
      v   = W gs
      du  = d1 pr u
      dv  = d1 pr v
      sgn = if odd (degW p u) then p-1 else 1
  in addPoly pr (mulRightW pr du v) (scalePoly pr sgn (mulLeftW pr u dv))

--------------------------------------------------------------------------------
-- Adem (odd p) → admissible NF
--------------------------------------------------------------------------------

signPow :: Prime -> Int -> Int
signPow pr k = if even k then 1 else unP pr - 1
{-# INLINE signPow #-}

ademPair :: Prime -> Gen -> Gen -> Maybe Poly
ademPair pr@(OddP p) a b =
  case (a,b) of
    (Lam ai, Lam bj) ->
      if ai >= p * bj + 1 then Nothing else Just (ademLL ai bj)
    (Lam ai, Mu  bj) ->
      if ai >= p * bj + 1 then Nothing else Just (ademLM ai bj)
    (Mu  ai, Lam bj) ->
      if ai >= p * bj + 1 then Nothing else Just (ademML ai bj)
    (Mu  ai, Mu  bj) ->
      if ai >= p * bj     then Nothing else Just (ademMM ai bj)
  where
    ademLL a b =
      let tMax = a `div` p
          terms = concat
            [ let chooseTop = (p-1)*(b - t) - 1
                  chooseBot = a - p*t - 1
              in if chooseTop < 0 || chooseBot < 0
                    then []
                    else
                      let c = binomModP p chooseTop chooseBot
                          s = signPow pr (a + t)
                      in [ ( W [Lam (a + b - t)] >< W [Lam t]
                           , mulP pr s c) ]
            | t <- [0 .. tMax]
            ]
      in normalizePoly pr $ M.fromListWith (addP pr) terms

    ademLM a b =
      let tMax = a `div` p
          terms = concat
            [ let chooseTop = (p-1)*(b - t)
                  chooseBot = a - p*t - 1
              in if chooseTop < 0 || chooseBot < 0
                    then []
                    else
                      let c = binomModP p chooseTop chooseBot
                          s = signPow pr (a + t)
                      in [ ( W [Lam (a + b - t)] >< W [Mu t]
                           , mulP pr s c) ]
            | t <- [0 .. tMax]
            ]
      in normalizePoly pr $ M.fromListWith (addP pr) terms

    ademML a b =
      let tMax = a `div` p
          terms = concat
            [ let chooseTop = (p-1)*(b - t)
                  chooseBot = a - p*t - 1
              in if chooseTop < 0 || chooseBot < 0
                    then []
                    else
                      let c = binomModP p chooseTop chooseBot
                          s = signPow pr (a + t + 1)
                      in [ ( W [Mu (a + b - t)] >< W [Lam t]
                           , mulP pr s c) ]
            | t <- [0 .. tMax]
            ]
      in normalizePoly pr $ M.fromListWith (addP pr) terms

    ademMM a b =
      let tMax = a `div` p
          terms = concat
            [ let chooseTop = (p-1)*(b - t)
                  chooseBot = a - p*t
              in if chooseTop < 0 || chooseBot < 0
                    then []
                    else
                      let c = binomModP p chooseTop chooseBot
                          s = signPow pr (a + t)
                      in [ ( W [Mu (a + b - t)] >< W [Mu t]
                           , mulP pr s c) ]
            | t <- [0 .. tMax]
            ]
      in normalizePoly pr $ M.fromListWith (addP pr) terms

reduceWordOnce :: Prime -> WordL -> Poly
reduceWordOnce pr (W xs) = go xs
  where
    go (x:y:rest) =
      case ademPair pr x y of
        Just polyPair ->
          normalizePoly pr $
            M.fromListWith (addP pr)
              [ (w >< W rest, c) | (w,c) <- M.toList polyPair ]
        Nothing ->
          let tailRed = reduceWordOnce pr (W (y:rest))
          in if M.null tailRed
                then mono pr 1 (W (x:y:rest))
                else normalizePoly pr $
                     M.fromListWith (addP pr)
                       [ (W (x:ws), c) | (W ws, c) <- M.toList tailRed ]
    go _ = mono pr 1 (W xs)

reduceWordFull :: Prime -> WordL -> Poly
reduceWordFull pr w0 = loop (mono pr 1 w0)
  where
    loop poly =
      let step = normalizePoly pr $
                   M.fromListWith (addP pr)
                     [ (w', mulP pr c c')
                     | (w,c)   <- M.toList poly
                     , (w',c') <- M.toList (reduceWordOnce pr w)
                     ]
      in if step == poly then poly else loop step

-- Parallelized: process monomials independently
reducePolyFull :: Prime -> Poly -> Poly
reducePolyFull pr poly =
  normalizePoly pr $
    M.fromListWith (addP pr) $
      concat $
        parMap rdeepseq
          (\(w,c) -> [ (w', mulP pr c c') | (w',c') <- M.toList (reduceWordFull pr w) ])
          (M.toList poly)

toAdmissible :: Prime -> WordL -> Poly
toAdmissible = reduceWordFull

--------------------------------------------------------------------------------
-- Basis by degree (built once) — parallelized batched reductions
--------------------------------------------------------------------------------

gensUpTo :: Int -> Int -> [Gen]
gensUpTo p cap =
  let ls = takeWhile (\(i,_) -> 2*i*(p-1)-1 <= cap) [ (i, Lam (i-1)) | i <- [1..] ]
      ms = takeWhile (\(i,_) -> 2*i*(p-1)   <= cap) [ (i, Mu  (i-1)) | i <- [1..] ]
  in map snd (ls ++ ms)

extendOne :: Prime -> Int -> Set WordL -> Set WordL
extendOne pr@(OddP p) cap ws =
  S.fromList
    [ W (unW w ++ [g])
    | w <- S.toList ws
    , g <- gensUpTo p (cap - degW p w)
    , degW p (W (unW w ++ [g])) <= cap
    ]

basisByDegree :: Prime -> Int -> Map Int (Set WordL)
basisByDegree pr@(OddP p) cap = grow (S.singleton (W [])) M.empty
  where
    insertReducedOne acc w' =
      let d = degW p w'
      in if d <= cap then M.insertWith S.union d (S.singleton w') acc else acc

    -- Batch reduce with parallelism
    insertReducedBatch =
      foldl' (\m poly ->
        foldl' (\m' (w',_) -> insertReducedOne m' w') m (M.toList poly))

    grow frontier acc =
      let next    = extendOne pr cap frontier
          reduced = parMap rdeepseq (reduceWordFull pr) (S.toList next)
          acc'    = insertReducedBatch acc reduced
      in if S.null next || S.size next == S.size frontier
           then M.delete 0 acc'
           else grow next acc'

buildBasisBundle
  :: Prime -> Int
  -> ( Map Int [WordL]         -- basis per degree (sorted)
     , Map Int (Map WordL Int) -- pos maps per degree
     )
buildBasisBundle pr cap =
  let table = basisByDegree pr cap
      lists = M.map (sort . S.toList) table
      pos   = M.map (\ws -> M.fromList (zip ws [0..])) lists
  in (lists, pos)

--------------------------------------------------------------------------------
-- Vectorized rank over F_p
--------------------------------------------------------------------------------

-- Reduce a column vector against existing pivots (each pivot is normalized)
reduceWithPivotsU :: Prime -> [(Int, Vector Int)] -> Vector Int -> Vector Int
reduceWithPivotsU pr pivots v0 =
  foldl' step v0 pivots
  where
    step v (!pi, !pv) =
      let a = if pi < U.length v then U.unsafeIndex v pi else 0
      in if a == 0
           then v
           else
             let s = modP pr (negate a)
                 pvScaled = U.map (mulP pr s) pv
             in U.zipWith (addP pr) v pvScaled
{-# INLINE reduceWithPivotsU #-}

firstNonZeroU :: Vector Int -> Maybe Int
firstNonZeroU v =
  let n = U.length v
      go !i | i >= n    = Nothing
            | otherwise = let x = U.unsafeIndex v i
                          in if x /= 0 then Just i else go (i+1)
  in go 0
{-# INLINE firstNonZeroU #-}

-- Column-wise rank for vectors represented as unboxed vectors
rankFromColumnsU :: Prime -> [Vector Int] -> Int
rankFromColumnsU pr cols0
  | null cols0 = 0
  | otherwise  =
      let rows   = U.length (head cols0)
          -- Ensure uniform length (truncate/pad); cheap guards
          fit v  = let lv = U.length v
                   in if lv == rows then v
                      else if lv < rows then v U.++ U.replicate (rows - lv) 0
                      else U.take rows v
          cols   = map fit cols0
          step (!pivots, !rk) v =
            let v' = reduceWithPivotsU pr pivots v
            in case firstNonZeroU v' of
                 Nothing -> (pivots, rk)
                 Just pi ->
                   let a   = U.unsafeIndex v' pi
                       inv = if a == 0 then 1 else invModPrime pr a
                       v'' = U.map (mulP pr inv) v'
                   in ((pi, v'') : pivots, rk + 1)
      in snd (foldl' step ([], 0 :: Int) cols)

-- Build one d^1 column as an unboxed vector of length |B_{d-1}|
buildD1ColumnU
  :: Prime
  -> Map Int (Map WordL Int) -- pos maps
  -> Int                      -- degree d
  -> WordL
  -> Vector Int
buildD1ColumnU pr posMaps d w =
  let bd1Map = M.findWithDefault M.empty (d-1) posMaps
      rows   = M.size bd1Map
      img    = reducePolyFull pr (d1 pr w)
      -- Collect (rowIdx, coeff) pairs and accumulate into a dense vector
      pairs  = [ (r, c)
               | (w',c) <- M.toList img
               , Just r <- [M.lookup w' bd1Map] ]
  in U.accum (addP pr) (U.replicate rows 0) pairs

-- Column-wise rank of d^1_d (vectorized & parallelized)
rankD1DegreeColumnwise
  :: Prime
  -> Map Int [WordL]
  -> Map Int (Map WordL Int)
  -> Int
  -> Int
rankD1DegreeColumnwise pr basisLists posMaps d =
  let bd   = M.findWithDefault [] d     basisLists
      rows = M.size (M.findWithDefault M.empty (d-1) posMaps)
  in if null bd || rows == 0
       then 0
       else
         let cols = parMap rdeepseq (buildD1ColumnU pr posMaps d) bd
         in rankFromColumnsU pr cols

-- Row-wise rank (rank equals rank of transpose). Build rows as dense vectors.
rankD1DegreeRowwise
  :: Prime
  -> Map Int [WordL]
  -> Map Int (Map WordL Int)
  -> Int
  -> Int
rankD1DegreeRowwise pr basisLists posMaps d =
  let bd    = M.findWithDefault [] d       basisLists  -- columns
      bd1   = M.findWithDefault [] (d-1)   basisLists  -- rows
      rows  = length bd1
      cols  = length bd
  in if cols == 0 || rows == 0
       then 0
       else
         let imgs :: [Poly]
             imgs = parMap rdeepseq (reducePolyFull pr . d1 pr) bd
             coeffIn :: WordL -> Poly -> Int
             coeffIn = M.findWithDefault 0
             rowVecU :: WordL -> Vector Int
             rowVecU r = U.fromListN cols (map (coeffIn r) imgs)
             rowVectors = parMap rdeepseq rowVecU bd1
         in rankFromColumnsU pr rowVectors

-- Adaptive choice
rankD1Degree
  :: Prime
  -> Map Int [WordL]
  -> Map Int (Map WordL Int)
  -> Int
  -> Int
rankD1Degree pr basisLists posMaps d =
  let rows = length (M.findWithDefault [] (d-1) basisLists)
      cols = length (M.findWithDefault [] d       basisLists)
  in if cols < rows
       then rankD1DegreeRowwise   pr basisLists posMaps d
       else rankD1DegreeColumnwise pr basisLists posMaps d

-- Image dimension of d^1_{d+1}
imRankD1Next
  :: Prime
  -> Map Int [WordL]
  -> Map Int (Map WordL Int)
  -> Int
  -> Int
imRankD1Next pr basisLists posMaps d =
  if M.member (d+1) basisLists && not (null (M.findWithDefault [] (d+1) basisLists))
    then rankD1Degree pr basisLists posMaps (d+1)
    else 0

--------------------------------------------------------------------------------
-- Reports / IO
--------------------------------------------------------------------------------

showPoly :: Prime -> Poly -> String
showPoly pr mp0 =
  let mp = normalizePoly pr mp0
  in if M.null mp then "0"
     else intercalate " + "
            [ let c' = modP pr c
              in (if c' == 1 then "" else show c' ++ "*") ++ show w
            | (w,c) <- M.toList mp ]

reportDegree
  :: Prime
  -> Map Int [WordL]
  -> Map Int (Map WordL Int)
  -> Int
  -> IO ()
reportDegree pr basisLists posMaps d = do
  let bd      = M.findWithDefault [] d basisLists
      dimV    = length bd
      rk      = rankD1Degree pr basisLists posMaps d
      dimKer  = dimV - rk
      dimImN1 = imRankD1Next pr basisLists posMaps d
      dimH    = dimKer - dimImN1
  putStrLn $ "-- degree " ++ show d
  putStrLn $ "  dim V_d         = " ++ show dimV
  putStrLn $ "  rank d^1_d      = " ++ show rk
  putStrLn $ "  dim ker d^1_d   = " ++ show dimKer
  putStrLn $ "  dim im d^1_{d+1}= " ++ show dimImN1
  putStrLn $ "  dim H_d         = " ++ show dimH

reportRange :: Prime -> Int -> IO ()
reportRange pr cap = do
  putStrLn $ "=== d^1-matrix homology report over F_" ++ show (unP pr)
          ++ " for degrees <= " ++ show cap
  let (basisLists, posMaps) = buildBasisBundle pr cap
      degrees = filter (>0) (M.keys basisLists)
  mapM_ (reportDegree pr basisLists posMaps) degrees

--------------------------------------------------------------------------------
-- Demos / parsing
--------------------------------------------------------------------------------

stripPrefixASCII :: String -> String -> Maybe String
stripPrefixASCII pre s =
  if map toLower pre == map toLower (take (length pre) s)
    then Just (drop (length pre) s) else Nothing

parseGen :: String -> Maybe Gen
parseGen s
  | Just rest <- stripPrefixASCII "lambda" s, all isDigit rest = Just (Lam (read rest - 1))
  | Just rest <- stripPrefixASCII "mu"     s, all isDigit rest = Just (Mu  (read rest - 1))
  | otherwise = Nothing

parseWord :: String -> Maybe WordL
parseWord raw =
  let toks = filter (not . null) (words raw)
  in if null toks then Just (W []) else W <$> mapM parseGen toks

testLucas :: IO ()
testLucas = do
  putStrLn "== Lucas cache (p=3) =="
  print (binomModP 3 5 2 == 1)
  print (binomModP 3 6 3 == 2)
  print (binomModP 3 3 1 == 0)
  print (binomModP 3 4 2 == 0)

testD1 :: IO ()
testD1 = do
  let pr = OddP 3
  putStrLn "== d^1 sanity (p=3) =="
  putStrLn $ "d(lambda2) = " ++ showPoly pr (d1 pr (W [Lam 1]))
  putStrLn $ "d(mu1)     = " ++ showPoly pr (d1 pr (W [Mu 0]))

demoAdem :: IO ()
demoAdem = do
  let pr = OddP 3
  putStrLn "== Adem quick (p=3) =="
  putStrLn $ "reduce(lambda3 * lambda4) = " ++ showPoly pr (toAdmissible pr (W [Lam 2] >< W [Lam 3]))
  putStrLn $ "reduce(lambda4 * mu1)     = " ++ showPoly pr (toAdmissible pr (W [Lam 3] >< W [Mu 0]))
  putStrLn $ "reduce(mu1 * lambda4)     = " ++ showPoly pr (toAdmissible pr (W [Mu 0]  >< W [Lam 3]))

printBasisTable :: Prime -> Int -> Bool -> IO ()
printBasisTable pr cap withD1 = do
  putStrLn $ "=== Basis over F_" ++ show (unP pr) ++ " up to degree " ++ show cap ++ " ==="
  let (basisLists, _) = buildBasisBundle pr cap
  mapM_ (\(deg, ws) -> do
           putStrLn $ "-- degree " ++ show deg ++ " :"
           mapM_ (\w -> do
                    putStrLn $ "  " ++ show w
                    when withD1 $ do
                        let rhs = reducePolyFull pr (d1 pr w)
                        putStrLn $ "    d^1 = " ++ showPoly pr rhs
                 ) ws
        ) (M.toList basisLists)
  putStrLn ""

runLambdaTests :: IO ()
runLambdaTests = do
  testLucas
  testD1
  demoAdem
  printBasisTable (OddP 3) 24 False
  reportRange (OddP 3) 40
