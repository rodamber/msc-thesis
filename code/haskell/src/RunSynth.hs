module RunSynth
  (OptNumExamples(..),
   OptNumConsts(..),
   OptFile(..),
   Opts(..),
   optNumExamples,
   optNumConsts,
   optFile,
   runSynth,
   main) where

import           Options.Applicative
import           System.TimeIt

import           Components
import           ReadExample
import           Synth
import           Types


newtype OptNumExamples = OptNumExamples Int
newtype OptNumConsts = OptNumConsts Int
newtype OptFile = OptFile FilePath

data Opts = Opts OptNumExamples OptNumConsts OptFile


numExamples :: Opts -> Int
numExamples (Opts (OptNumExamples e) _ _) = e


numConsts :: Opts -> Int
numConsts (Opts _ (OptNumConsts c) _) = c


file :: Opts -> FilePath
file (Opts _ _ (OptFile f)) = f


opts :: Parser Opts
opts = Opts <$> optNumExamples <*> optNumConsts <*> optFile


optNumExamples :: Parser OptNumExamples
optNumExamples = OptNumExamples <$>
  option auto (long "examples" <>
               short 'e' <>
               metavar "EXAMPLES" <>
               showDefault <>
               value 1 <>
               help "How many examples to use")


optNumConsts :: Parser OptNumConsts
optNumConsts = OptNumConsts <$>
  option auto (long "constants" <>
               short 'c' <>
               metavar "CONSTANTS" <>
               showDefault <>
               value 1 <>
               help "Maximum number of constants to use")


optFile :: Parser OptFile
optFile = OptFile <$> strArgument (metavar "FILE")


optsInfo :: ParserInfo Opts
optsInfo = info (opts <**> helper)
           (fullDesc <>
            header "outsynth2 -- a PBE synthesizer for OutSystems expressions")


lib :: [Component]
lib = [ concat_
      , index_
      , length_
      -- , replace_
      , substr_
      -- , tolower_
      -- , toupper_
      -- , trim_
      -- , trim_start_
      -- , trim_end_
      , add_
      , sub_
      ]


runSynth :: Opts -> IO ()
runSynth opts = do
      examples <- take (numExamples opts) <$>
                  readExamplesFromFile (file opts)

      putStrLn $ "=== Examples (" <> file opts <> ")"
      mapM_ (putStrLn . showExample) examples

      putStrLn "=== Library"
      mapM_ (putStrLn . name) lib

      putStrLn "=== Synthesis"
      timeIt $ synthesize lib (numConsts opts) examples


main :: IO ()
main = runSynth =<< execParser optsInfo
