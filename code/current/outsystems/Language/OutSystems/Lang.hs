module Language.OutSystems.Lang where

import Relude (Bool, Int, Text)

import Language.OutSystems.Cast


-- * Language ------------------------------------------------------------------

class (LangText f, LangBool f, LangArith f) => Lang0 f

class LangText f where
  int       :: Int    -> f Int
  text      :: Text   -> f Text

  length    :: f Text -> f Int
  substr    :: f Text -> f Int  -> f Int -> f Text
  concat    :: f Text -> f Text -> f Text
  chr       :: f Int -> f Text
  index0    :: f Text -> f Text -> f Int
  index1    :: f Text -> f Text -> f Int -> f Int
  replace   :: f Text -> f Text -> f Text -> f Text
  lower     :: f Text -> f Text
  upper     :: f Text -> f Text
  trimEnd   :: f Text -> f Text
  trimStart :: f Text -> f Text
  trim      :: f Text -> f Text

class LangBool f where
  bool    :: Bool -> f Bool

  if_     :: f Bool -> f a -> f a -> f a
  or      :: f Bool -> f Bool -> f Bool
  not     :: f Bool -> f Bool

  eqBool  :: f Bool -> f Bool -> f Bool
  eqText  :: f Text -> f Text -> f Bool
  eqInt   :: f Int  -> f Int  -> f Bool

  leqText :: f Text -> f Text -> f Bool
  leqInt  :: f Int  -> f Int  -> f Bool

class LangArith f where
  uminus :: f Int -> f Int

  minus  :: f Int -> f Int -> f Int
  plus   :: f Int -> f Int -> f Int
  mult   :: f Int -> f Int -> f Int
  div    :: f Int -> f Int -> f Int
