module Examples.Expressions where

import           Data.Text (Text)
--------------------------------------------------------------------------------
-- | Language Grammar

-- FIXME: Should probably expect arithmetic expressions where Int is specified.
-- FIXME: Doesn't handle optional values
data Expr
  = Lit                Text
  | Chr       { _c  :: Int }
  | Concat    { _t1 :: Expr, _t2     :: Expr }
  | Index     { _t  :: Expr, _search :: Expr, _startIndex :: Int, _searchFromEnd :: Bool, _ignoreCase :: Bool }
  | Length    { _t  :: Expr }
  | NewLine
  | Replace   { _t  :: Expr, _search :: Expr, _replace    :: Expr }
  | Substr    { _t  :: Expr, _start  :: Int,  _length     :: Int  }
  | ToLower   { _t  :: Expr }
  | ToUpper   { _t  :: Expr }
  | Trim      { _t  :: Expr }
  | TrimEnd   { _t  :: Expr }
  | TrimStart { _t  :: Expr }
  deriving (Show)

