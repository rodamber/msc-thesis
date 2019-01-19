import Prelude

import qualified OutSystems as OS
import Counter

import GHC.Base (String)
import Text.Printf (printf)


howMany :: [OS.Expression] -> Int -> Int -> IO ()
howMany expressions lower upper = do
  let c :: Counter Int ; c = count $ map (length . OS.funs) expressions
  let atLeast n = sum $ map (`lookup` c) [n .. upper]

  for_ [lower .. upper] $ \i -> do
    let fmt = "There are %d expressions that use %d or more functions.\n"
    printf fmt (atLeast i) i


printTop :: Show a => [(a, Int)] -> IO ()
printTop xs = for_ (zip [1..] xs) $ \ (i, (x, n)) ->
  printf "%d. %s (%d)\n" (i :: Int) (show x :: String) n


main :: IO ()
main = do
  es <- OS.expressions "data/exprs.jsonl"
  howMany es 0 13


-- -- FIXME: We're not considering expressions that return identifiers
-- -- FIXME: We're not considering operators
