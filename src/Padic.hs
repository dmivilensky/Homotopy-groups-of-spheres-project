{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

--
-- * Core valuations: 'vpZ' (integers), 'vpQ' (rationals), 'splitPower' (n = p^k * m).
-- * p-adic norm '|·|_p' and RL projections: 'projRe', 'projPad', 'projClip'.
-- * Path composition / scoring for weights: 'combineWeights', 'scoreWeight'.
-- * Factorial/binomial valuations (Legendre), Lucas helpers and C(n,k) mod p:
--     'vpFactorial', 'vpBinom', 'lucasDigits', 'binomIsZeroModP', 'binomModP'.
-- * Unit part (remove p-power), modular inverse modulo p^k, Hensel lifting:
--     'unitPart', 'invModPrimePow', 'henselSimple'.
-- * Small vector aggregates useful as dense features: 'vpVectorMin', 'padicNormMax'.
-- * Tests: 'runPadicTests' (and a 'main' that calls it), using 'assert' only.
--

module Padic (runPadicTests) where

import           Control.Exception        (assert)
import           Data.Ratio
import           GHC.Generics             (Generic)
import qualified Data.Text                as T
import           Data.Text                (Text)

--------------------------------------------------------------------------------
-- Core p-adic primitives
--------------------------------------------------------------------------------

-- | p-adic valuation on integers. Returns a large sentinel for 0 representing +∞.
vpZ :: Integer -> Integer -> Int
vpZ _ 0 = maxBound `div` 4
vpZ p n
  | p < 2     = error "vpZ: p must be >= 2"
  | otherwise = go 0 (abs n)
  where
    go k m =
      case m `quotRem` p of
        (q,0) -> go (k+1) q
        _     -> k

-- | Decompose n = p^k * m with p ∤ m. The sign of m follows n.
splitPower :: Integer -> Integer -> (Int, Integer)
splitPower p n
  | n == 0    = (vpZ p 0, 0)
  | otherwise = let k = vpZ p n; d = p^k in (k, n `div` d)

-- | p-adic valuation on rationals.
vpQ :: Integer -> Rational -> Int
vpQ p q
  | q == 0    = vpZ p 0
  | otherwise = vpZ p (numerator q) - vpZ p (denominator q)

-- | p-adic norm on rationals: |q|_p = p^{-v_p(q)}. For q=0 returns Infinity.
padicNormQ :: Integer -> Rational -> Double
padicNormQ p q
  | q == 0    = 1/0
  | otherwise = (fromIntegral p) ** fromIntegral (negate (vpQ p q))

-- Projections used on the RL side ------------------------------------------------

projRe   :: Rational -> Double
projRe = fromRational

-- | projPad p q = - v_p(q) (so larger => “more p-adically small”).
projPad  :: Integer -> Rational -> Int
projPad p = negate . vpQ p

-- | Clip |a/b| ≤ T preserving sign.
projClip :: Double -> Rational -> Double
projClip t r
  | t <= 0    = 0
  | otherwise = max (-t) (min t (fromRational r))

--------------------------------------------------------------------------------
-- JSON helpers and edge weights
--------------------------------------------------------------------------------

-- | Encode a 'Rational' as a Text @"a/b"@ in lowest terms.
ratToText :: Rational -> Text
ratToText q = let a = numerator q; b = denominator q
              in T.pack (show a ++ "/" ++ show b)

-- | Decode a Text @"a/b"@ (or @"a"@) into a 'Rational'. Returns 'Nothing' on ill-formed input.
ratFromText :: Text -> Maybe Rational
ratFromText t =
  case T.splitOn (T.pack "/") (T.strip t) of
    [a]   -> (%%) <$> readI a <*> pure 1
    [a,b] -> (%%) <$> readI a <*> readI b
    _     -> Nothing
  where
    (%%) x y | y == 0    = 1 % 0
             | otherwise = x % y
    readI s = case reads (T.unpack s) of
                [(n,"")] -> Just n
                _        -> Nothing

-- | Weight carried by Bridge graph edges: real-valued cost and a p-adic valuation component.
-- The alpha is serialised as \"a/b\".
data Weight = Weight
  { alpha :: Rational
  , vp    :: Int
  } deriving (Eq, Show, Generic)

-- | Path semantics: sum of alphas, minimum of valuations.
combineWeights :: [Weight] -> Weight
combineWeights = foldr step (Weight 0 (maxBound `div` 4))
  where
    step (Weight a v) (Weight a' v') = Weight (a + a') (min v v')

-- | Map a weight into a scalar score: cA * Re(alpha) + cV * max(0, -vp).
scoreWeight :: Double -> Double -> Weight -> Double
scoreWeight cA cV (Weight a v) = cA * fromRational a + cV * fromIntegral (max 0 (-v))

--------------------------------------------------------------------------------
-- Factorials, binomials (Legendre), Lucas helpers and C(n,k) mod p
--------------------------------------------------------------------------------

-- | Legendre's formula: v_p(n!) = sum_{i≥1} floor(n / p^i).
vpFactorial :: Integer -> Integer -> Int
vpFactorial p n
  | n < 0     = error "vpFactorial: n must be >= 0"
  | otherwise = go 0 p
  where
    go acc pk
      | pk > n    = acc
      | otherwise = go (acc + fromIntegral (n `div` pk)) (pk * p)

-- | v_p(C(n,k)) computed via Legendre.
vpBinom :: Integer -> Integer -> Integer -> Int
vpBinom p n k
  | k < 0 || k > n = vpZ p 0   -- convention: C(n,k)=0 ⇒ v_p(0)=+∞
  | otherwise      = vpFactorial p n - vpFactorial p k - vpFactorial p (n-k)

-- | Base-p digits (least-significant first).
lucasDigits :: Integer -> Integer -> [Int]
lucasDigits p n
  | p < 2     = error "lucasDigits: p must be >= 2"
  | n < 0     = error "lucasDigits: n must be >= 0"
  | n == 0    = [0]
  | otherwise = go n []
  where
    go 0 acc = if null acc then [0] else acc
    go m acc = let (q,r) = m `quotRem` p in go q (fromIntegral r : acc)

-- | Lucas criterion (zero-test): C(n,k) ≡ 0 (mod p) iff some digit k_i > n_i in base p.
binomIsZeroModP :: Integer -> Integer -> Integer -> Bool
binomIsZeroModP p n k
  | k < 0 || k > n = True
  | otherwise      =
      let nd = reverse (lucasDigits p n)
          kd = reverse (lucasDigits p k)
          pad xs l = replicate (l - length xs) 0 ++ xs
          l  = max (length nd) (length kd)
          nd' = pad nd l
          kd' = pad kd l
      in any id [ ki > ni | (ni,ki) <- zip nd' kd' ]

-- | Small nCk modulo prime p using Lucas theorem with per-digit factorials.
binomModP :: Integer -> Integer -> Integer -> Integer
binomModP p n k
  | p <= 1    = error "binomModP: p must be prime >= 2"
  | k < 0 || k > n = 0
  | otherwise =
      let nd = reverse (lucasDigits p n)
          kd = reverse (lucasDigits p k)
          l  = max (length nd) (length kd)
          pad xs = replicate (l - length xs) 0 ++ xs
          nd' = pad nd
          kd' = pad kd
      in foldl (\acc (ni,ki) -> (acc * chooseSmall ni ki) `mod` p) 1 (zip nd' kd')
  where
    chooseSmall ni ki
      | ki < 0 || ki > ni = 0
      | otherwise =
          let num = factMod ni
              den = (factMod ki * factMod (ni - ki)) `mod` p
              inv = modPow p den (fromIntegral (p-2))
          in (num * inv) `mod` p
    factMod m = foldl (\a x -> (a * x) `mod` p) 1 [1..(fromIntegral m)]

--------------------------------------------------------------------------------
-- Units, modular inverse modulo p^k, Hensel lifting
--------------------------------------------------------------------------------

-- | Unit part of n relative to p: u such that n = p^v * u with p ∤ u.
unitPart :: Integer -> Integer -> Integer
unitPart p n = let (_, m) = splitPower p n in m

-- | Fast exponentiation modulo m (m ≥ 1).
modPow :: Integer -> Integer -> Integer -> Integer
modPow m _ 0 = 1 `mod` m
modPow m a e
  | e < 0     = error "modPow: negative exponent"
  | otherwise = go (a `mod` m) e 1
  where
    go _ 0 acc = acc
    go b k acc
      | odd k     = go ((b*b) `mod` m) (k `div` 2) ((acc*b) `mod` m)
      | otherwise = go ((b*b) `mod` m) (k `div` 2) acc

-- | Inverse of a modulo p^k, assuming gcd(a,p)=1 and p prime.
-- Implemented via lifting of the congruence a*x ≡ 1.
invModPrimePow :: Integer -> Int -> Integer -> Integer
invModPrimePow p k a
  | k <= 0        = error "invModPrimePow: k must be >= 1"
  | gcd a p /= 1  = error "invModPrimePow: a not invertible modulo p^k"
  | otherwise     = go 1 x1
  where
    x1 = modPow p (a `mod` p) (fromIntegral (p-2))  -- a^(p-2) mod p
    go i xi
      | i >= k    = xi `mod` (p^k)
      | otherwise =
          let m   = p^i
              m'  = p^(i+1)
              -- Solve a*(xi + m*t) ≡ 1 mod m' ⇒ a*m*t ≡ 1 - a*xi (mod m')
              rhs = (1 - (a*xi) `mod` m') `mod` m'
              t   = ((rhs `div` m) * modPow p (a `mod` p) (fromIntegral (p-2))) `mod` p
              xi' = (xi + m * t) `mod` m'
          in go (i+1) xi'

-- | Hensel lifting for a simple root: given f, f', prime p, a0 with
--   f(a0) ≡ 0 (mod p) and p ∤ f'(a0), produce a_k modulo p^k.
henselSimple :: (Integer -> Integer)   -- ^ f
             -> (Integer -> Integer)   -- ^ f'
             -> Integer                -- ^ prime p
             -> Integer                -- ^ a0 (mod p)
             -> Int                    -- ^ k (target power)
             -> Integer                -- ^ a_k (mod p^k)
henselSimple f f' p a0 k
  | k <= 1    = a0 `mod` p
  | otherwise = go 1 (a0 `mod` p)
  where
    go i ai
      | i >= k    = ai `mod` (p^k)
      | otherwise =
          let m   = p^i
              m'  = p^(i+1)
              fi  = f ai
              fpi = f' ai
              num = (negate (fi `div` m)) `mod` p
              den = (fpi `mod` p)
              inv = modPow p den (fromIntegral (p-2))
              t   = (num * inv) `mod` p
              ai' = (ai + m * t) `mod` m'
          in go (i+1) ai'

--------------------------------------------------------------------------------
-- Small vector projections/aggregates (handy for features)
--------------------------------------------------------------------------------

-- | Minimum v_p over a rational vector (∞ treated as very large integer).
vpVectorMin :: Integer -> [Rational] -> Int
vpVectorMin p = minimum . map (vpQ p)

-- | Maximum p-adic norm over a rational vector (|0|_p = ∞ yields Infinity).
padicNormMax :: Integer -> [Rational] -> Double
padicNormMax p = maximum . map (padicNormQ p)

--------------------------------------------------------------------------------
-- TESTS (callable from main)
--------------------------------------------------------------------------------

assertTrue :: String -> Bool -> IO ()
assertTrue msg cond = do
  let _ = assert cond ()
  putStrLn ("[ok] " ++ msg)

assertEq :: (Show a, Eq a) => String -> a -> a -> IO ()
assertEq msg x y = do
  let _ = assert (x == y) ()
  putStrLn ("[ok] " ++ msg ++ ": " ++ show x)

testValuations :: IO ()
testValuations = do
  assertTrue "vpZ(3,0) is big" (vpZ 3 0 > 10)
  assertEq   "vpZ(3,9)=2" (vpZ 3 9) 2
  assertEq   "vpZ(5,250)=3" (vpZ 5 250) 3
  assertEq   "vpQ(3,27/2)=3" (vpQ 3 (27 % 2)) 3
  assertEq   "padicNormQ 2 (3/8)=8" (round (padicNormQ 2 (3 % 8))) 8
  let (k',m') = splitPower 3 162
  assertEq   "splitPower 3 162 -> (4,2)" (k',m') (4,2)

testBinomLucas :: IO ()
testBinomLucas = do
  assertEq "vpFactorial 3 6 = 2" (vpFactorial 3 6) 2
  assertEq "vpBinom 3 6 3 = 0" (vpBinom 3 6 3) 0
  let n = 10; k = 4; p = 3
  -- C(10,4)=210 ≡ 0 mod 3; Lucas zero-test should say True
  assertTrue "binomIsZeroModP (3,10,4)" (binomIsZeroModP p n k)
  -- A case that is not zero: C(10,1)=10 ≡ 1 mod 3
  assertTrue "binomIsZeroModP (3,10,1) == False" (not (binomIsZeroModP p 10 1))
  assertEq "binomModP 3 10 4 = 0" (binomModP 3 10 4) 0
  assertEq "binomModP 3 10 1 = 1" (binomModP 3 10 1) 1

testHenselAndInv :: IO ()
testHenselAndInv = do
  -- Hensel: solve x^2 - 1 ≡ 0 mod 3, lift root a0=1 to mod 3^5
  let p  = 3
      k  = 5
      f  x = x*x - 1
      fp x = 2*x
      a0 = 1
      ak = henselSimple f fp p a0 k
      m  = p^k
  assertEq "henselSimple x^2-1 at p=3 to mod 3^5" ((f ak) `mod` m) 0
  -- inverse modulo p^k
  let a = 10
      inv = invModPrimePow p k a
  assertTrue "invModPrimePow works" (((a*inv) `mod` (p^k)) == (1 `mod` (p^k)))

testVecAgg :: IO ()
testVecAgg = do
  let xs = [1 % 9, 2 % 3, 0, 5]
  assertEq "vpVectorMin p=3" (vpVectorMin 3 xs) (minimum (map (vpQ 3) xs))
  assertTrue "padicNormMax >= individual" (padicNormMax 3 xs >= maximum (map (padicNormQ 3) xs))

-- | Aggregate runner (exported). Use from your project or via `runghc -main-is Padic.main Padic.hs`.
runPadicTests :: IO ()
runPadicTests = do
  putStrLn "Running Padic test suite..."
  testValuations
  testBinomLucas
  testHenselAndInv
  testVecAgg
  putStrLn "All Padic tests finished."
