module Examples.Parser where

import           Prelude                    hiding (concat, length)

import           Examples.Expressions

import           Control.Monad.Combinators
import           Data.Text                  (Text)
import qualified Data.Text                  as T
import           Data.Void
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L


-- FIXME: Handle escaped characters
-- FIXME: Signeds
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

signed :: Parser Int
signed = L.signed spaceConsumer int

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

expr :: Parser Expr
expr = lit <|> chr <|> concat  <|> index <|> length  <|> newLine <|> replace <|>
    substr <|> toLower  <|> toUpper <|> trim  <|> trimEnd <|> trimStart
  where
    lit = Lit . T.pack <$> (char '"' >> manyTill L.charLiteral (char '"'))

    template :: Text -> Parser Expr -> Parser Expr
    template name p = symbol name >> parens p

    chr       = template "Chr"       (Chr       <$> int)
    concat    = template "Concat"    (Concat    <$> expr <*> comma expr)
    index     = template "Index"
        (Index <$> expr <*> comma expr <*> comma int <*> comma bool <*> comma bool)
    length    = template "Length"    (Length    <$> expr)
    newLine   = template "NewLine"   (NewLine   <$  empty)
    replace   = template "Replace"   (Replace   <$> expr <*> comma expr <*> comma expr)
    substr    = template "Substr"    (Substr    <$> expr <*> comma int  <*> comma int)
    toLower   = template "ToLower"   (ToLower   <$> expr)
    toUpper   = template "ToUpper"   (ToUpper   <$> expr)
    trim      = template "Trim"      (Trim      <$> expr)
    trimEnd   = template "TrimEnd"   (TrimEnd   <$> expr)
    trimStart = template "TrimStart" (TrimStart <$> expr)

