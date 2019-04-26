module Language.OutSystems.Evaluator where

import Relude

import Language.OutSystems.Lang ()


-- * Evaluator -----------------------------------------------------------------

newtype Eval a = Eval { eval :: a }

