module Examples.Expressions
  -- ( TextExpr(..)
  -- , IntExpr(..)
  -- , evalT
  -- , evalI
  -- )
where

import           Data.Text (Text)

--------------------------------------------------------------------------------
-- | DSL Grammar

-- NOTE: Consider applying recursion schemes.
-- NOTE: Should probably expect arithmetic expressions where Int is specified.
-- NOTE: Consider expressing a diferent language than this one. In particular,
-- consider separating monolithic functions (like Index) into sub functions
-- (that don't necessarily exist in the OutSystems library).

-- FIXME: Doesn't handle optional/default values (AFAIK only occurs in Index).

data Expr = TExpr TextExpr | IExpr IntExpr deriving (Show)

data TextExpr
  = TLit      Text
  | Chr       IntExpr
  -- ^        charcode
  | Concat    TextExpr TextExpr
  | NewLine
  | Replace   TextExpr TextExpr TextExpr
  -- ^        t        search   replace
  | Substr    TextExpr IntExpr  IntExpr
  -- ^        t        start    length
  | ToLower   TextExpr
  | ToUpper   TextExpr
  | Trim      TextExpr
  | TrimEnd   TextExpr
  | TrimStart TextExpr
  deriving (Show)

data CaseSensitivity = Sensitive | Insensitive deriving (Eq, Ord, Show)
data SearchDirection = FromStart | FromEnd     deriving (Eq, Ord, Show)

data IntExpr
  = ILit   Int
  | Index  TextExpr TextExpr IntExpr SearchDirection CaseSensitivity
  -- ^     t        search   startIndex
  -- ^ FIXME: There is a corner case related to aggregates.
  -- ^ FIXME: There is a corner case related to the search direction.
  | Length TextExpr
  deriving (Show)

