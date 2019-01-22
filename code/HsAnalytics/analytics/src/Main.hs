import Relude

import qualified OutSystems as OS
import Counter

import GHC.Base (String)
import Text.Printf (printf)

import Data.Aeson (encode)


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


main :: IO ()
main = do
  es <- OS.expressions "../data/exprs.jsonl"
  -- inBetween (length . OS.funs) es 0 13

  for_ es $ \e -> do
    let len = length $ OS.funs e
    when (3 <= len && len <= 6) $
      putLBSLn $ encode e
    

  


-- -- FIXME: We're not considering expressions that return identifiers
-- -- FIXME: We're not considering operators
