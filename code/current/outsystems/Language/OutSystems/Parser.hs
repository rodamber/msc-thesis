--------------------------------------------------------------------------------
-- Parser for our limited subset of Outsystems expressions

module Language.OutSystems.Parser where

import           Relude                         hiding (bool, chr, concat,
                                                 length, not, or)

import qualified Language.OutSystems.Pretty

import           Control.Monad.Combinators
import           Control.Monad.Combinators.Expr
import           Data.Text                      (Text)
import qualified Data.Text                      as T
import           Data.Void
import           Text.Megaparsec                as MP
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer     as L

--------------------------------------------------------------------------------
-- AST

data LTExp
  = Int Int
  | Text Text
  | Fun1 Fun1 LTExp
  | Fun2 Fun2 LTExp LTExp
  | Fun3 Fun3 LTExp LTExp LTExp
  deriving (Show)

data Fun1
  = Length
  | Chr
  | Lower
  | Upper
  | TrimEnd
  | TrimStart
  | Trim
  deriving (Show)

data Fun2
  = Concat
  | Index0
  deriving (Show)

data Fun3
  = Substr
  | Index1
  | Replace
  deriving (Show)

--------------------------------------------------------------------------------
-- Lexemes

type Parser = Parsec Void Text

spaceConsumer :: Parser ()
spaceConsumer = L.space space1 empty empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

symbol :: Text -> Parser Text
symbol = L.symbol spaceConsumer

--------------------------------------------------------------------------------
-- Combinators

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

comma :: Parser a -> Parser a
comma p = symbol "," *> p

funname :: Text -> Parser a -> Parser a
funname name p = string name *> parens p

fun1 :: Text -> Fun1 -> Parser LTExp
fun1 name f = funname name args1
  where args1 = Fun1 f <$> parser

fun2 :: Text -> Fun2 -> Parser LTExp
fun2 name f = funname name args2
  where args2 = Fun2 f <$> parser <*> comma parser

fun3 :: Text -> Fun3 -> Parser LTExp
fun3 name f = funname name args3
  where args3 = Fun3 f <$> parser <*> comma parser <*> parser

--------------------------------------------------------------------------------
-- Operators

-- operators :: OpExpr f => [[Operator Parser (f Dynamic)]]
-- operators =
--   [ [ prefix "-"   _UMinus ]
--   , [ prefix "not" _Not    ]
--   , [ binary "*"   _Mult
--     , binary "/"   _Div    ]
--   , [ binary "+"   _Plus
--     , binary "-"   _BMinus ]
--   , [ binary "<="  _Leq    ]
--   , [ binary "="   _Eq     ]
--   , [ binary "or"  _Or     ]
--   ]

-- binary  name f = InfixL  (f <$ symbol name)
-- prefix  name f = Prefix  (f <$ symbol name)

-- opExpr :: Parser OpExpr
-- opExpr = makeExprParser opTerm operators

-- opTerm :: Parser OpExpr

--------------------------------------------------------------------------------
-- Parser

int :: Parser LTExp
int = Int <$> lexeme L.decimal

text :: Parser LTExp
text = let quote = char '\"' in Text . T.pack <$>
    (quote >> manyTill latin1Char quote)

length, chr, lower, upper, trimEnd, trimStart, trim :: Parser LTExp
length    = fun1 "Length" Length
chr       = fun1 "Chr" Chr
lower     = fun1 "Lower" Lower
upper     = fun1 "Upper" Upper
trimEnd   = fun1 "TrimEnd" TrimEnd
trimStart = fun1 "TrimStart" TrimStart
trim      = fun1 "Trim" Trim

concat, index0 :: Parser LTExp
concat = fun2 "Concat" Concat
index0 = fun2 "Index0" Index0

index1, substr, replace :: Parser LTExp
index1  = fun3 "Index1" Index1
substr  = fun3 "Substr" Substr
replace = fun3 "Replace" Replace

parser :: Parser LTExp
parser = asum
  [ int, text
  , length, chr, lower, upper, trimEnd, trimStart, trim
  , concat, index0, index1, substr, replace
  ]

