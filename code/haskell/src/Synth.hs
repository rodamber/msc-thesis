module Synth where

import           Constraints
import           Types

import           Control.Monad.Reader
import           Data.List
import           Data.Maybe
import           Data.SBV         hiding (name)
import           Data.SBV.Control

synthesize :: Library -> Int -> [Example] -> IO ()
synthesize lib constCount ios = loop 1
  where
    -- timeout_value = 5 * 60 * 10^6

    loop componentCount = do
      putStrLn $ "size: " <> show componentCount

      let cfg = Config { examples = ios
                       , library = lib
                       , constCount = constCount
                       , componentCount = componentCount
                       }

      satRes  <-runSMT $ do
        res <- runReaderT formula cfg
        query $ -- timeout timeout_value $
          checkSat >>= \x -> do
          case x of
            Sat -> do
              io $ putStr "Program: "
              io . putStrLn =<< extractProgram cfg res
            Unk -> io . print =<< getUnknownReason
            _ -> return ()
          return x

      case satRes of
        Sat -> return ()
        _   -> loop (componentCount + 1)


extractProgram :: Config -> Result -> Query String
extractProgram cfg res = do
  let inputCount = length $ fst $ head $ examples cfg
      nameit pre x = pre <> show x

      inputNames = map (nameit "x") [0 .. inputCount - 1]
      constNames = map (nameit "c") [0 .. constCount cfg - 1]
      resNames   = map (nameit "r") [0 .. componentCount cfg - 1]

      line2name =
        zip [1 .. inputCount] inputNames <>
        zip [inputCount + 1 .. inputCount + constCount cfg] constNames <>
        zip [inputCount + constCount cfg + 1 ..] resNames

  consts <- map (either id show) <$> mapM getValue (resConsts res)
  comps <- map (name . ((library cfg !!) . subtract 1) . fromIntegral) <$>
           mapM getValue (resActivs res)
  locss <- map catMaybes <$> mapM (mapM getValue) (resLocations res)

  let topLine = "prog(" <> intercalate ", " inputNames <> "):"
  let constLines = zipWith (\c n -> n <> " = " <> show c) consts constNames
  let resLines = flip map (zip3 resNames comps locss) $ \(r, f, ls) ->
        let params = map (fromJust . flip lookup line2name . fromIntegral) ls
        in r <> " = " <> f <> "(" <> intercalate ", " params  <> ")"

  let indent n = map (replicate n ' ' <>)

  return $ unlines $ [topLine] <> indent 2 (constLines <> resLines)
