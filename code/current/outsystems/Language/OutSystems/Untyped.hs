{-# LANGUAGE FlexibleInstances #-}
module Language.OutSystems.Untyped where


import Relude hiding ((+))

import Language.OutSystems.Cast
import qualified Language.OutSystems.Lang as Typed

import Data.Tree

-- * Language ------------------------------------------------------------------

class Lang0 a where
  intL     :: Int    -> a
  textL    :: Text   -> a
  lengthL  :: a -> a
  substrL  :: a -> a -> a -> a -> a
  trimL    :: a -> a
  replaceL :: a -> a -> a -> a


instance Lang0 (Tree Text) where
  intL x          = Node (show x)  []
  textL x         = Node (show x)  []
  lengthL x       = Node "Length"  [x]
  substrL x y z w = Node "Substr"  [x, y, z, w]
  trimL x         = Node "Trim"    [x]
  replaceL x y z  = Node "Replace" [x, y, z]
