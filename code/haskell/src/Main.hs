module Main where

import           Types

import           Control.Monad
import           Data.Either
import           System.TimeIt


main = undefined


showE = either show show
showEs = concat . map showE


bench :: [Example] -> Library -> IO ()
bench ios lib = do
  let constCount = 4
  let synthesize = undefined

  putStrLn "Examples:"

  forM_ ios $ \(is, o) ->
    putStrLn ("\t" <> showEs is <> " --> " <> showE o)

  timeIt $ synthesize ios lib constCount

  putStrLn "=================================================="
