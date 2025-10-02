{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE BlockArguments  #-}

module Main (main) where

import           Control.Monad              (forM_)
import qualified Data.Aeson                 as A
import qualified Data.ByteString.Lazy.Char8 as BL
import           Data.Char                  (isSpace)
import           Data.List                  (intercalate)
import qualified Data.Map.Strict            as M
import           Data.Maybe                 (fromMaybe)
import           Options.Applicative
import           System.IO                  (IOMode (WriteMode), hPutStrLn, withFile)
import           System.Directory (createDirectoryIfMissing)
import           System.FilePath  (takeDirectory)

-- Локальные модули
import qualified Lambda
import qualified Bridge
import qualified WuModel

--------------------------------------------------------------------------------
-- CLI options
--------------------------------------------------------------------------------

data Opts = Opts
  { optPrime     :: Int
  , optCap       :: Int
  , optClass     :: Int
  , optBchW      :: Int
  , optThetaK    :: Int
  , optPadicP    :: Maybe Integer
  , optWordsFile :: Maybe FilePath
  , optPreset    :: Maybe String
  , optEmitFile  :: FilePath
  , optLogFile   :: FilePath
  , optGenPerDeg :: Maybe Int
  , optDegMin    :: Maybe Int
  , optDegMax    :: Maybe Int
  }

optsP :: Parser Opts
optsP = Opts
  <$> option auto (long "prime"  <> short 'p' <> help "odd prime for Lambda" <> value 3)
  <*> option auto (long "cap"    <> short 'd' <> help "degree cap in Lambda"  <> value 40)
  <*> option auto (long "class"  <> short 'c' <> help "Hall nilpotency class" <> value 6)
  <*> option auto (long "bch"                <> help "BCH truncation order (2 or 3)" <> value 3)
  <*> option auto (long "theta-k"<> short 'k'<> help "theta arity (number of Hall leaves used)" <> value 3)
  <*> optional (option auto (long "padic"     <> help "p-adic prime for summaries"))
  <*> optional (strOption    (long "words"    <> short 'w' <> help "file with words (one per line)"))
  <*> optional (strOption    (long "preset"   <> help "presentation preset: Torus | Surface:<g>"))
  <*> strOption (long "emit-words" <> help "path to write generated words" <> value "./data/generated.txt")
  <*> strOption (long "log-stats" <> help "path to log stats" <> value "./data/stats.json")
  <*> optional (option auto (long "gen-per-degree" <> help "max words per degree (default: all)"))
  <*> optional (option auto (long "deg-min"        <> help "min degree to emit (default: 1)"))
  <*> optional (option auto (long "deg-max"        <> help "max degree to emit (default: cap)"))

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  Opts{..} <- execParser $ info (optsP <**> helper)
                               (fullDesc <> progDesc "Linear pipeline runner: auto-generate Lambda words, quantize via Bridge, emit JSON")

  -- Prime (как значение и как тип Lambda.Prime)
  let pPrime = Lambda.OddP optPrime
      capD   = optCap
      cls    = optClass
      bchW   = if optBchW <= 2 then Bridge.BCH_Trunc2 else Bridge.BCH_Trunc3
      thetaQ = Bridge.thetaQInitCanon optThetaK
      degMin = fromMaybe 1    optDegMin
      degMax = fromMaybe capD optDegMax
  
  createDirectoryIfMissing True (takeDirectory optEmitFile)
  createDirectoryIfMissing True (takeDirectory optLogFile)

  -- 1) строим admissible-базы по степеням
  let (basisLists, _posMaps) = Lambda.buildBasisBundle pPrime capD

  -- 2) формируем список слов из баз по степеням (строго admissible)
  let generatedWords = emitWordsFromBasis basisLists degMin degMax optGenPerDeg

  -- 3) записываем список в файл (для воспроизводимости)
  writeWordsFile optEmitFile generatedWords

  -- 4) источник слов для прогона: если задан --words, используем его; иначе — только что сгенерированный список
  wordsIn <- case optWordsFile of
    Just path -> lines <$> readFile path
    Nothing   -> pure generatedWords

  -- 5) линейный конвейер над wordsIn
  payloads <- mapM (runOne pPrime capD cls bchW thetaQ optPadicP) wordsIn

  -- 6) опциональная Fox/SNF диагностика на шаблоне (например, Torus или Surface:g)
  foxObj <- case optPreset of
    Nothing -> pure A.Null
    Just s  -> runFoxPreset s

  -- 7) выводим JSON-результаты
  let json =
        A.encode $
          A.object
            [ "prime"     A..= optPrime
            , "cap"       A..= capD
            , "class"     A..= cls
            , "bch"       A..= optBchW
            , "theta_k"   A..= optThetaK
            , "emitted"   A..= A.object
                [ "file"      A..= optEmitFile
                , "count"     A..= length generatedWords
                , "degMin"    A..= degMin
                , "degMax"    A..= degMax
                , "perDegree" A..= optGenPerDeg
                ]
            , "wordsUsed" A..= length wordsIn
            , "results"   A..= payloads
            , "foxPreset" A..= foxObj
            ]

  BL.writeFile optLogFile json
  putStrLn $ "JSON сохранён в: " ++ optLogFile
  putStrLn $ "Слова сохранены в: " ++ optEmitFile
--------------------------------------------------------------------------------
-- Линейный шаг пайплайна для одного слова
--------------------------------------------------------------------------------

runOne
  :: Lambda.Prime
  -> Int                 -- cap
  -> Int                 -- class
  -> Bridge.BCHMode
  -> Bridge.ThetaQ
  -> Maybe Integer       -- padic prime
  -> String              -- raw word (text)
  -> IO A.Value
runOne p capD cls bchMode thetaQ mp s =
  case Lambda.parseWord s of
    Nothing -> pure $ A.object [ "raw" A..= s, "parse" A..= ("error" :: String) ]
    Just w  -> do
      let deg = Lambda.degW (Lambda.unP p) w
      if deg > capD
        then pure $ A.object [ "raw" A..= s, "deg" A..= deg, "skipped" A..= True ]
        else do
          let (_gnf, qs) = Bridge.quantizeViaBCHFast cls bchMode thetaQ w
              padicInfo  = case mp of
                             Nothing   -> A.Null
                             Just padp ->
                               let (_g2, qsP) = Bridge.quantizeViaBCHWithPadic cls bchMode padp thetaQ w
                               in A.toJSON (quantStatsToJSON qsP)
          pure $ A.object
            [ "raw"   A..= s
            , "deg"   A..= deg
            , "stats" A..= quantStatsToJSON qs
            , "padic" A..= padicInfo
            ]

--------------------------------------------------------------------------------
-- Генерация и запись списка слов из admissible-баз
--------------------------------------------------------------------------------

emitWordsFromBasis
  :: M.Map Int [Lambda.WordL]  -- degree -> admissible words
  -> Int                       -- degMin
  -> Int                       -- degMax
  -> Maybe Int                 -- per-degree cap
  -> [String]
emitWordsFromBasis basisLists dMin dMax mCap =
  concatMap oneDeg [dMin .. dMax]
  where
    oneDeg d =
      case M.lookup d basisLists of
        Nothing -> []
        Just ws ->
          let takeN = maybe id take mCap
          in map renderWordText (takeN ws)

    -- красивый вывод слов (строки вида "lambda3 mu1 ...")
    renderWordText :: Lambda.WordL -> String
    renderWordText = Lambda.renderWord

writeWordsFile :: FilePath -> [String] -> IO ()
writeWordsFile path ws =
  withFile path WriteMode $ \h ->
    forM_ ws (hPutStrLn h . trim)
  where
    trim = f . f
      where f = reverse . dropWhile isSpace

--------------------------------------------------------------------------------
-- Fox/SNF диагностика для типовых презентаций (через WuModel)
--------------------------------------------------------------------------------

data Preset = PresetTorus | PresetSurface Int | PresetUnknown

parsePreset :: String -> Preset
parsePreset s =
  case break (==':') s of
    ("Torus",   "")         -> PresetTorus
    ("Surface", ':' : rest) ->
      case reads rest of
        [(g,"")] -> PresetSurface g
        _        -> PresetUnknown
    _ -> PresetUnknown

runFoxPreset :: String -> IO A.Value
runFoxPreset tag =
  case parsePreset tag of
    PresetTorus -> do
      let pres = WuModel.buildFromTemplate WuModel.Torus
          j    = WuModel.foxJacobianZ pres
          (freeRank, tors) = WuModel.h1Invariants pres
      pure $ A.object
        [ "preset" A..= ("Torus" :: String)
        , "J"      A..= j
        , "H1"     A..= A.object [ "free" A..= freeRank, "torsion" A..= tors ]
        ]
    PresetSurface g -> do
      let pres = WuModel.buildFromTemplate (WuModel.Surface g)
          j    = WuModel.foxJacobianZ pres
          (freeRank, tors) = WuModel.h1Invariants pres
      pure $ A.object
        [ "preset" A..= ("Surface" :: String)
        , "g"      A..= g
        , "J"      A..= j
        , "H1"     A..= A.object [ "free" A..= freeRank, "torsion" A..= tors ]
        ]
    PresetUnknown ->
      pure $ A.object [ "preset" A..= tag, "error" A..= ("unknown" :: String) ]

--------------------------------------------------------------------------------
-- JSON helpers
--------------------------------------------------------------------------------

quantStatsToJSON :: Bridge.QuantStats -> A.Value
quantStatsToJSON qs =
  A.object
    [ "byWeight"         A..= Bridge.qsByWeight qs
    , "surrogateSupport" A..= Bridge.qsSuppNF   qs
    ]
