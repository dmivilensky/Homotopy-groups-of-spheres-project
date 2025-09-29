module Main (main) where

import qualified WuModel as W
import qualified Fox as F
import qualified Hall as H
import qualified Padic as P
import qualified Lambda as L

main :: IO ()
main = do
--   L.runLambdaTests
--   F.runFoxTests
--   H.runHallTests
--   P.runPadicTests
  W.runWuTests
