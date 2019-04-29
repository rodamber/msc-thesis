module RunBench where

import           Control.Monad
import           System.Directory
import           System.Process

import           Options.Applicative

import qualified RunSynth            as S hiding (main)


data Opts = Opts
  Int -- ^ wall-clock time limit in seconds
  Int -- ^ memory limit in gigabytes
  FilePath -- ^ output directory
  [S.OptFile] -- ^ files with examples
  S.OptNumExamples -- ^ number of examples to take from each benchmark
  S.OptNumConsts -- ^ number of constants to use


timeLimit (Opts t _ _ _ _ _) = t
memLimit (Opts _ m _ _ _ _) = m
outputDir (Opts _ _ d _ _ _) = d
files (Opts _ _ _ fs _ _) = fs
numExamples (Opts _ _ _ _ (S.OptNumExamples e) _) = e
numConsts (Opts _ _ _ _ _ (S.OptNumConsts c)) = c


opts :: Parser Opts
opts = Opts <$>
  optTimeLimit <*>
  optMemLimit <*>
  optOutputDir <*>
  some S.optFile <*>
  S.optNumExamples <*>
  S.optNumConsts


optTimeLimit :: Parser Int
optTimeLimit = option auto (long "time-limit" <>
                            short 't' <>
                            metavar "TIME-LIMIT" <>
                            showDefault <>
                            value 1 <>
                            help "Time limit (wall-clock time) in seconds")


optMemLimit :: Parser Int
optMemLimit = option auto (long "mem-limit" <>
                           short 'm' <>
                           metavar "MEM-LIMIT" <>
                           showDefault <>
                           value 12 <>
                           help "Memory limit in gigabytes")


optOutputDir :: Parser FilePath
optOutputDir = strOption (long "output-dir" <>
                          short 'd' <>
                          metavar "OUTPUT-DIR" <>
                          help "Directory where to save the benchmarks")


optsInfo :: ParserInfo Opts
optsInfo = info (opts <**> helper)
           (fullDesc <> header "outsynth2 benchmark runner")


ensureRunsolver :: IO ()
ensureRunsolver = void $ readProcess "which" ["runsolver"] ""


runBench :: Opts -> IO ()
runBench opts = do
  ensureRunsolver

  createDirectoryIfMissing True (outputDir opts)

  forM_ (files opts) $ \(S.OptFile file) ->
    readProcess "runsolver" [ "--wall-clock-limit"
                            , show $ timeLimit opts
                            , "--mem-limit"
                            , show $ memLimit opts * 1000 -- megabytes
                            , "--solver-data"
                            , outputDir opts <> "/" <> file <> ".out"
                            , "--timestamp"
                            , "outsynth2"
                            , "--examples"
                            , show $ numExamples opts
                            , "--constants"
                            , show $ numConsts opts
                            , file
                            ] ""


main :: IO ()
main = runBench =<< execParser optsInfo
