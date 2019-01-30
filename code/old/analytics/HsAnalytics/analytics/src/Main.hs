{-# LANGUAGE TypeApplications #-}
import Relude

import qualified OutSystems as OS
import Counter

import GHC.Base (String)
import Text.Printf (printf)

import Control.Exception.Base (assert)
import Data.Aeson (decode, encode)


inBetween :: (OS.Expression -> Int) -> [OS.Expression] -> Int -> Int -> IO ()
inBetween f expressions lower upper = do
  let c = count $ map f expressions
  let atLeast n = sum $ map (`lookup` c) [n .. upper]

  for_ [lower .. upper] $ \i -> do
    let fmt = "There are %d expressions that use %d or more functions.\n"
    printf fmt (atLeast i) i


printTop :: Show a => [(a, Int)] -> IO ()
printTop xs = for_ (zip [1..] xs) $ \(i, (x, n)) ->
  printf "%d. %s (%d)\n" (i :: Int) (show x :: String) n

analyze36 :: IO ()
analyze36 = do
  es <- OS.expressions "exprs-3-6.jsonl"
  printf "Number of expressions: %d\n" (length es)
  inBetween (length . OS.funs) es 0 13

main :: IO ()
main = do
  analyze36
  -- es <- OS.expressions "../data/exprs.jsonl"

  -- let Just e = viaNonEmpty head es
  -- print e
  -- putLBSLn $ encode e
  -- print $ decode @OS.Expression (encode e)

  -- for_ es $ \e -> do
  --   let len = length $ OS.funs e
  --   when (3 <= len && len <= 6) $
  --     putLBSLn $ encode e
    

  


-- -- FIXME: We're not considering expressions that return identifiers
-- -- FIXME: We're not considering operators
