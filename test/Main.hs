module Main (main) where

import qualified WuModel as W
import qualified Fox as F
import qualified Hall as H
import qualified Padic as P
import qualified Lambda as L
import qualified Bridge as B

main :: IO ()
main = do
  L.runLambdaTests
  -- H.runHallTests
  -- B.runBridgeTests
  -- F.runFoxTests
  -- P.runPadicTests
  -- W.runWuTests
