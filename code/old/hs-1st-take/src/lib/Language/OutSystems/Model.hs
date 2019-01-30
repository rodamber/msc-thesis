{-# LANGUAGE GADTs #-}

-- | Modeling DSL that captures the semantics of the built-in functions of the
-- OutSystems language. This is the the language whose programs we are going to
-- synthesize.

module Language.OutSystems.Model where

import Data.Text (Text)

type Name = Text

-- TODO: This is just a simple sketch
data Term
  = Var Name
  | Lit
  | Chr Term
  | Concat Term Term
  | Length Term
  | NewLine
  | Replace
  | Substr
  | ToLower
  | ToUpper
  | Trim
  | TrimEnd
  | TrimStart
  -- | Extra
  | Reverse
  | Search
  -- | Non-obvious
  -- | Index Term Term
  deriving (Eq, Ord, Show)
