{-# LANGUAGE LambdaCase        #-}

module Counter where

import Protolude

import qualified Data.Map as M

type Counter k = Map k Int

init :: Map k a
init = M.empty

count :: (Foldable t, Ord k) => t k -> Counter k
count = foldl' (flip inc) init

lookup :: Ord k => k -> Counter k -> Int
lookup = M.findWithDefault 0

inc :: Ord k => k -> Counter k -> Counter k
inc = M.alter $ \case
  Nothing -> Just 1
  Just x ->  Just (x + 1)

top :: Ord k => Int -> Counter k -> [(k, Int)]
top n = take n . sortOn (Down . snd) . M.assocs
