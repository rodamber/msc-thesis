module Main where

import           Options.Applicative
import           System.TimeIt

import           Components
import           ReadExample
import           Synth
import           Types


data Opts = Opts { numExamples :: Int
                 , numConsts   :: Int
                 , file        :: FilePath
                 , version     :: Bool }


opts :: Parser Opts
opts = Opts
  <$> option auto ( long "examples"
                 <> short 'e'
                 <> metavar "EXAMPLES"
                 <> showDefault
                 <> value 1
                 <> help "How many examples to use")
  <*> option auto ( long "constants"
                 <> short 'c'
                 <> metavar "CONSTANTS"
                 <> showDefault
                 <> value 1
                 <> help "Maximum number of constants to use")
  <*> strOption ( long "file"
               <> short 'f'
               <> metavar "FILE"
               <> help "File to read from")
  <*> switch ( long "version"
            <> short 'v'
            <> help "Print version number")


optsInfo :: ParserInfo Opts
optsInfo = info (opts <**> helper)
           ( fullDesc
          <> progDesc "Haskell synthesizer"
          <> header "outsynth1 -- a PBE synthesizer for OutSystems expressions")


lib :: [Component]
lib = [ concat_
      , length_
      , replace_
      , substr_
      , tolower_
      , toupper_
      , trim_
      , trim_start_
      , trim_end_
      , add_
      , sub_]


runSynth :: Opts -> IO ()
runSynth opts
  | version opts = putStrLn "OutSystems expression synthesizer version 2"
  | otherwise = do
      examples <- readExamplesFromFile (file opts)

      putStrLn "=== Examples"
      mapM_ (putStrLn . showExample) examples

      putStrLn "=== Library"
      mapM_ (putStrLn . name) lib

      putStrLn "=== Synthesis"
      timeIt $ synthesize lib (numConsts opts) examples


main :: IO ()
main = runSynth =<< execParser optsInfo
