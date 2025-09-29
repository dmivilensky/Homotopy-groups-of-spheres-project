{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- Lambda.hs
-- Lambda algebra over F_p (odd p)
--  * Generators λ_i, μ_i (internal 0-based; printed 1-based)
--  * d^1 (deg -1), graded Leibniz
--  * Odd-prime Adem relations (LL/LM/ML/MM) → Curtis admissible NF
--  * Basis by degree (built once up to cap)
--  * Homology report using adaptive rank:
--      - column-wise Gaussian rank if rows ≤ cols
--      - row-wise (via transpose idea) if cols < rows
--  * Lucas binomial with per-prime cached factorials/invfactorials
--  * 100% safe indexing (no raw (!!))

module Lambda where

import qualified Data.Map.Strict as M
import           Data.Map.Strict (Map)
import qualified Data.Set        as S
import           Data.Set        (Set)
import           Data.List       (intercalate, sortBy)
import           Data.Char       (isDigit, toLower)

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
  | e `mod` 2 == 0 = let t = powMod a (e `div` 2) m in (t*t) `mod` m
  | otherwise      = (a `mod` m) * powMod a (e-1) m `mod` m

invModPrime :: Prime -> Int -> Int
invModPrime pr@(OddP p) a = powMod (modP pr a) (p-2) p

--------------------------------------------------------------------------------
-- Safe indexing helpers (no raw (!!))
--------------------------------------------------------------------------------

getAt :: [a] -> Int -> Maybe a
getAt xs i
  | i < 0    = Nothing
  | otherwise = go xs i
  where
    go [] _       = Nothing
    go (y:_)  0   = Just y
    go (_:ys) k   = go ys (k-1)

getAtD :: a -> [a] -> Int -> a
getAtD def xs i = maybe def id (getAt xs i)

setAt :: Int -> a -> [a] -> [a]
setAt i a xs
  | i < 0          = xs
  | otherwise      = go xs i
  where
    go [] _        = []
    go (_:ys) 0    = a : ys
    go (y:ys) k    = y : go ys (k-1)

--------------------------------------------------------------------------------
-- Lambda.Core: gens/words/polys
--------------------------------------------------------------------------------

data Gen = Lam !Int | Mu !Int deriving (Eq, Ord)

instance Show Gen where
  show (Lam i) = "lambda" ++ show (i+1)
  show (Mu  i) = "mu"     ++ show (i+1)

newtype WordL = W { unW :: [Gen] } deriving (Eq, Ord)

instance Show WordL where
  show (W [])   = "1"
  show (W gens) = intercalate " " (map show gens)

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

zeroPoly :: Poly
zeroPoly = M.empty

mono :: Prime -> Int -> WordL -> Poly
mono pr c w = normalizePoly pr (M.singleton w c)

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

mulRightW :: Prime -> Poly -> WordL -> Poly
mulRightW pr poly w =
  normalizePoly pr $ M.fromListWith (addP pr)
    [ (w1 >< w, c) | (w1,c) <- M.toList poly ]

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
      let facts = scanl (\a b -> (a*b) `mod` p) 1 [1..p-1]
          inv x = powMod x (p-2) p
          invfacts = 0 : map (\i -> inv (facts !! i)) [1..p-1]
      let v = (facts, invfacts)
      writeIORef lucasCacheRef (M.insert p v m)
      pure v

smallChooseCached :: Int -> [Int] -> [Int] -> Int -> Int -> Int
smallChooseCached p facts invfacts n k
  | k < 0 || k > n = 0
  | otherwise      = (((facts !! n) * (invfacts !! k)) `mod` p) * (invfacts !! (n-k)) `mod` p

binomModP :: Int -> Int -> Int -> Int
binomModP p n k
  | k < 0 || k > n = 0
  | otherwise =
      let (facts, invfacts) = getLucasTables p
          dsN = digitsBase p n
          dsK = digitsBase p k
          f ni ki =
            if ki > ni then 0 else smallChooseCached p facts invfacts ni ki
      in foldl (\acc (ni,ki) -> (acc * f ni ki) `mod` p) 1 (zip dsN (dsK ++ repeat 0))

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

d1 :: Prime -> WordL -> Poly
d1 pr@(OddP p) (W [])     = zeroPoly
d1 pr           (W [g])   = d1Gen pr (W [g])
d1 pr@(OddP p)  (W (g:gs)) =
  let u   = W [g]
      v   = W gs
      du  = d1 pr u
      dv  = d1 pr v
      sgn = if odd (degW p u) then (p-1) else 1
  in addPoly pr (mulRightW pr du v) (scalePoly pr sgn (mulLeftW pr u dv))

--------------------------------------------------------------------------------
-- Adem (odd p) → admissible NF
--------------------------------------------------------------------------------

signPow :: Prime -> Int -> Int
signPow pr k = if even k then 1 else (unP pr - 1)

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

reducePolyFull :: Prime -> Poly -> Poly
reducePolyFull pr poly =
  normalizePoly pr $
    M.fromListWith (addP pr)
      (concat
        [ [ (w', mulP pr c c') | (w',c') <- M.toList (reduceWordFull pr w) ]
        | (w,c) <- M.toList poly
        ])

toAdmissible :: Prime -> WordL -> Poly
toAdmissible = reduceWordFull

--------------------------------------------------------------------------------
-- Basis by degree (built once)
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
    insertReduced acc w =
      let red = reduceWordFull pr w
      in foldl
           (\m (w',_) ->
              let d = degW p w'
              in if d <= cap
                   then M.insertWith S.union d (S.singleton w') m
                   else m)
           acc (M.toList red)

    grow frontier acc =
      let next = extendOne pr cap frontier
          acc' = S.foldl' insertReduced acc next
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
      lists = M.map (sortBy compare . S.toList) table
      pos   = M.map (\ws -> M.fromList (zip ws [0..])) lists
  in (lists, pos)

--------------------------------------------------------------------------------
-- Rank: column-wise (default) and row-wise (when cols < rows)
--------------------------------------------------------------------------------

-- Reduce a vector against existing pivots (list of (pivotIdx, pivotVec))
reduceWithPivots :: Prime -> [(Int,[Int])] -> [Int] -> [Int]
reduceWithPivots pr pivots v0 =
  foldl
    (\v (pi, pv) ->
        let a = getAtD 0 v pi
        in if a == 0 then v
           else
             let s = modP pr (negate a)
             in zipWith (addP pr) v (map (mulP pr s) pv))
    v0 pivots

firstNonZero :: [Int] -> Maybe Int
firstNonZero = go 0
  where
    go _ []     = Nothing
    go i (x:xs) = if x /= 0 then Just i else go (i+1) xs

-- Column-wise rank: vectors are columns of length = rows
rankFromColumns :: Prime -> [[Int]] -> Int
rankFromColumns pr cols =
  let rows = if null cols then 0 else length (head cols)
      fit n v = let lv = length v in if lv==n then v else if lv<n then v ++ replicate (n-lv) 0 else take n v
      colsN   = map (fit rows) cols
      step (pivots, rk) v =
        let v' = reduceWithPivots pr pivots v
        in case firstNonZero v' of
             Nothing  -> (pivots, rk)
             Just pi  ->
               let a   = getAtD 0 v' pi
                   inv = if a == 0 then 1 else invModPrime pr a
                   v'' = map (mulP pr inv) v'
               in ((pi, v'') : pivots, rk + 1)
  in snd (foldl step ([], 0) colsN)

-- Build one d^1 column (length = |B_{d-1}|) for word w in degree d
buildD1Column
  :: Prime
  -> Map Int (Map WordL Int) -- pos maps
  -> Int
  -> WordL
  -> [Int]
buildD1Column pr posMaps d w =
  let bd1Map = M.findWithDefault M.empty (d-1) posMaps
      rows   = M.size bd1Map
      img    = reducePolyFull pr (d1 pr w)
      v0     = replicate rows 0
  in foldl
       (\vec (w',c) ->
          case M.lookup w' bd1Map of
            Nothing -> vec
            Just r  -> if r >= 0 && r < rows
                         then setAt r (addP pr (getAtD 0 vec r) c) vec
                         else vec)
       v0 (M.toList img)

-- Column-wise rank of d^1_d
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
         let cols = map (buildD1Column pr posMaps d) bd
         in rankFromColumns pr cols

-- Row-wise rank of d^1_d when cols < rows:
--   1) precompute images of all columns (few)
--   2) for each row basis element r in B_{d-1}, build row vector length=cols by reading coefficients
--   3) rank of transpose = rank of original, so run rankFromColumns on these row vectors
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
         let -- precompute images for each column word (few)
             imgs :: [Poly]
             imgs = map (\w -> reducePolyFull pr (d1 pr w)) bd
             -- fast lookup: for row word r, produce vector [ coeff(r in img_j) | j ]
             coeffIn :: WordL -> Poly -> Int
             coeffIn r poly = M.findWithDefault 0 r poly
             rowVec :: WordL -> [Int]
             rowVec r = map (coeffIn r) imgs
             rowVectors = map rowVec bd1   -- each vector length = cols (small)
         in rankFromColumns pr rowVectors

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
       then rankD1DegreeRowwise  pr basisLists posMaps d
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
-- Reports
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
-- Demos
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
                    if withD1
                      then do
                        let rhs = reducePolyFull pr (d1 pr w)
                        putStrLn $ "    d^1 = " ++ showPoly pr rhs
                      else pure ()
                 ) ws
        ) (M.toList basisLists)
  putStrLn ""

main :: IO ()
main = do
  testLucas
  testD1
  demoAdem
  printBasisTable (OddP 3) 24 False
  reportRange (OddP 3) 40
