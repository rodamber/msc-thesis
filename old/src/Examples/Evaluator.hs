module Examples.Evaluator where

import           Examples.Expressions

import           Data.Char
import           Data.Text            (Text)
import qualified Data.Text            as T

--------------------------------------------------------------------------------
-- | DSL Semantics

evalT :: TextExpr -> Text
evalT (TLit t)       = t
evalT (Chr c)        = T.singleton (chr (evalI c))
evalT (Concat t1 t2) = evalT t1 <> evalT t2
evalT NewLine        = T.singleton '\n'
evalT (Replace t search replace) =
  T.replace (evalT search) (evalT replace) (evalT t)
evalT (Substr t start len) =
  T.take (evalI len) (T.drop (evalI start) (evalT t))
evalT (ToLower t)   = T.toLower (evalT t)
evalT (ToUpper t)   = T.toUpper (evalT t)
evalT (Trim t)      = T.strip (evalT t)
evalT (TrimEnd t)   = T.stripEnd (evalT t)
evalT (TrimStart t) = T.stripStart (evalT t)

evalI :: IntExpr -> Int
evalI (ILit x) = x
evalI (Index t search startIndex direction Insensitive) =
  evalI (Index (ToLower t) (ToLower search) startIndex direction Sensitive)
evalI (Index t search startIndex direction Sensitive) =
    if match == T.empty then -1 else T.length prefix
  where
    needle   = evalT search
    haystack = T.drop (evalI startIndex) (evalT t)

    (prefix, match) = case direction of
        FromStart -> T.breakOn    needle haystack
        FromEnd   -> T.breakOnEnd needle haystack
evalI (Length t) = T.length (evalT t)
