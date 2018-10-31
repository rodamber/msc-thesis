{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import           Examples.Generator

import           Control.Arrow      ((&&&))
import           Data.Function
import           Data.List
import           Data.Maybe
import           Data.Ratio
import qualified Data.Set           as S
import           Data.Text          as T (Text)
import           Text.Printf


exprsIO :: IO [Expression]
exprsIO = fromJust <$> decodeJSONLinesGZ "view-expressions.jsonlines.gz"


hist :: Ord a => [a] -> [(a, Int)]
hist xs = let xss = group xs
          in map (head &&& length) xss -- zip (map head xss) (map length xss)


analytics :: [Expression] -> IO ()
analytics es = do
    printf "Analytics:\n"

    let esCount = length es
    let typesCount = length (S.fromList (map exprType es))

    let (typesPercentage :: Int) = round (100 * (fromIntegral typesCount / fromIntegral esCount) :: Double)

    printf "There are %d expressions.\n" esCount
    printf "There are %d different types (%d%%)\n" typesCount typesPercentage

    printf ""


main :: IO ()
main = exprsIO >>= analytics

-- 226234 expressions (87.5%) have type "Text"
--   histogram of #functions per expression:
--     [(0,103062),(1,88477),(2,20863),(3,9980),(4,2074),(5,1122),(6,228),(7,43),(8,249),(9,26),(10,17),(11,72),(12,5),(13,16)]
--   of which 4786 only use a subset of the considered "valid" functions
--     histogram of #functions per expression:
--       [(0,0),(1,4033),(2,627),(3,117),(4,7),(5,2)]
--     there are no const functions and 1-ary functions take the lion share
--     "EncodeSql" is never called in this subset of expressions
--     [("Substr",1768),("Replace",868),("EncodeJavaScript",633),("ToUpper",517),("NewLine",360),("TrimEnd",301),("Trim",292),("ToLower",253),("TrimStart",200),("Length",190),("Index",109),("EncodeHtml",83),("Concat",38),("Chr",38),("EncodeUrl",26)]
