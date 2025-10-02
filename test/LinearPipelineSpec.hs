{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import           Test.Hspec
import           Control.Monad         (forM_)
import qualified Data.List            as L
import qualified Data.Map.Strict      as M

-- Локальные модули
import qualified Lambda
import qualified Hall
import qualified Bridge
import qualified WuModel

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "Linear pipeline (Lambda -> BCH -> GroupNF)" $ do
    it "parses, bounds degree, quantizes deterministically (p=3, cap=40, class=6, BCH≤3)" $ do
      let p      = Lambda.OddP 3
          capD   = 40
          cls    = 6
          bchM   = Bridge.BCH_Trunc3
          thetaQ = Bridge.thetaQInitCanon 3
          wordsS = ["lambda1", "lambda2 mu1", "lambda3 lambda2 mu1"]
      forM_ wordsS $ \s -> do
        case Lambda.parseWord s of
          Nothing -> expectationFailure $ "parse failed for: " ++ s
          Just w  -> do
            -- степень не превосходит cap
            let d = Lambda.degW (Lambda.unP p) w
            d `shouldSatisfy` (<= capD)

            -- детерминизм квантования и статистик
            let (gnf1, qs1) = Bridge.quantizeViaBCHFast cls bchM thetaQ w
            let (gnf2, qs2) = Bridge.quantizeViaBCHFast cls bchM thetaQ w
            show gnf1 `shouldBe` show gnf2
            Bridge.qsByWeight qs1 `shouldBe` Bridge.qsByWeight qs2
            Bridge.qsSuppNF   qs1 `shouldBe` Bridge.qsSuppNF   qs2
            Bridge.qsVpMin    qs1 `shouldBe` Bridge.qsVpMin    qs2

            -- идемпотентность коллекции: вставка нулевого LieZ не меняет NF
            let gnf' = Hall.insertLieZRight cls gnf1 Hall.zeroLZ
            show gnf' `shouldBe` show gnf1

  describe "Fox/SNF diagnostics on Torus" $ do
    it "H1(T^2) ≅ Z^2 (rank 2, no torsion)" $ do
      let pres = WuModel.buildFromTemplate WuModel.Torus
          j    = WuModel.foxJacobianZ pres
          (freeRank, tors) = WuModel.h1Invariants pres
      freeRank `shouldBe` 2
      tors     `shouldBe` []  -- без торсии
