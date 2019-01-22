{-# LANGUAGE GADTs #-}

module Language.OutSystems.Lang where

import Relude hiding ((+))
import Relude.Unsafe (fromJust)

import Language.OutSystems.Cast


-- * Language ------------------------------------------------------------------

class Lang0 f where
  intL     :: Int    -> f Int
  textL    :: Text   -> f Text
  lengthL  :: f Text -> f Int
  substrL  :: f Text -> f Int  -> f Int  -> f Int -> f Text
  trimL    :: f Text -> f Text
  replaceL :: f Text -> f Text -> f Text -> f Text

