module Examples.Parser where

import           Prelude                    hiding (concat, length)

import           Examples.Expressions

import           Control.Monad.Combinators
import qualified Data.Bool                  as B (bool)
import           Data.Text                  (Text)
import qualified Data.Text                  as T
import           Data.Void
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L


-- FIXME: Handle escaped characters
-- FIXME: (true/false) Are data constructors in lower or upper case?

type Parser = Parsec Void Text

spaceConsumer :: Parser ()
spaceConsumer = L.space space1 empty empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

symbol :: Text -> Parser Text
symbol = L.symbol spaceConsumer

--------------------------------------------------------------------------------
-- Lexemes

int :: Parser Int
int = lexeme L.decimal

true :: Parser Bool
true = True <$ symbol "True"

false :: Parser Bool
false = False <$ symbol "False"

bool :: Parser Bool
bool = true <|> false

--------------------------------------------------------------------------------
-- Combinators

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

comma :: Parser a -> Parser a
comma p = symbol "," >> lexeme p

--------------------------------------------------------------------------------
-- Parser

template :: Text -> Parser a -> Parser a
template name p = symbol name >> parens p

textExpr :: Parser TextExpr
textExpr = lit <|> chr <|> concat <|> newLine <|> replace <|> substr <|>
    toLower <|> toUpper <|> trim <|> trimEnd <|> trimStart
  where
    lit = TLit . T.pack <$> (char '"' >> manyTill L.charLiteral (char '"'))

    chr     = template "Chr"     (Chr     <$> intExpr)
    concat  = template "Concat"  (Concat  <$> textExpr <*> comma textExpr)
    newLine = template "NewLine" (NewLine <$ empty)
    replace = template "Replace" $ Replace
      <$> textExpr
      <*> comma textExpr
      <*> comma textExpr
    substr    = template "Substr" $ Substr
      <$> textExpr
      <*> comma intExpr
      <*> comma intExpr
    toLower   = template "ToLower"   (ToLower   <$> textExpr)
    toUpper   = template "ToUpper"   (ToUpper   <$> textExpr)
    trim      = template "Trim"      (Trim      <$> textExpr)
    trimEnd   = template "TrimEnd"   (TrimEnd   <$> textExpr)
    trimStart = template "TrimStart" (TrimStart <$> textExpr)

intExpr :: Parser IntExpr
intExpr = index <|> length
  where
    index = template "Index" $ Index
      <$> textExpr
      <*> comma textExpr
      <*> comma intExpr
      <*> (B.bool FromStart   FromEnd   <$> comma bool)
      <*> (B.bool Insensitive Sensitive <$> comma bool)
    length = template "Length" (Length    <$> textExpr)

parser :: Parser Expr
parser = (TExpr <$> textExpr) <|> (IExpr <$> intExpr)
