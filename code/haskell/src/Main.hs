module Main where

import           Control.Monad
import           System.Environment

import           System.TimeIt

import           Components
import           ReadExample
import           Synth
import           Types


main = getArgs >>= \[fileName] -> bench fileName


stdlib = [ concat_
         , length_
         , replace_
         , substr_
         , tolower_
         , toupper_
         , trim_
         , trim_start_
         , trim_end_
         , add_
         , sub_
         ]


constCount = 2


bench :: FilePath -> IO ()
bench fileName = timeIt $
  synthesize stdlib constCount . take 1 =<< readExamplesFromFile fileName
