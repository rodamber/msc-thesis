--------------------------------------------------------------------------------
-- Parser for our limited subset of Outsystems expressions

module Language.OutSystems.Parser where

import           Relude                         hiding (bool, chr, concat,
                                                 length, not, or)

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
  | Fun Fun [LTExp]
  deriving (Show)

data Fun
  = Length
  | Chr
  | Lower
  | Upper
  | TrimEnd
  | TrimStart
  | Trim
  | Concat
  | Index0
  | Substr
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

fun :: Text -> Fun -> Parser LTExp
fun name f = funname name args
  where args = Fun f <$> sepBy1 parser (char ',')
          

--------------------------------------------------------------------------------
-- Parser

int :: Parser LTExp
int = Int <$> lexeme L.decimal

text :: Parser LTExp
text = let quote = char '\"' in Text . T.pack <$>
    (quote *> manyTill latin1Char quote)

length, chr, lower, upper, trimEnd, trimStart, trim :: Parser LTExp
length    = fun "Length" Length
chr       = fun "Chr" Chr
lower     = fun "Lower" Lower
upper     = fun "Upper" Upper
trimEnd   = fun "TrimEnd" TrimEnd
trimStart = fun "TrimStart" TrimStart
trim      = fun "Trim" Trim

concat, index0 :: Parser LTExp
concat = fun "Concat" Concat
index0 = fun "Index0" Index0

index1, substr, replace :: Parser LTExp
index1  = fun "Index1" Index1
substr  = fun "Substr" Substr
replace = fun "Replace" Replace

parser :: Parser LTExp
parser = asum
  [ int, text
  , length, chr, lower, upper, trimEnd, trimStart, trim
  , concat, index0, index1, substr, replace
  ]

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

