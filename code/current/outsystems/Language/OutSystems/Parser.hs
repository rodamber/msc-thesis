--------------------------------------------------------------------------------
-- Parser for our limited subset of Outsystems expressions

module Language.OutSystems.Parser where

import           Relude                         hiding (bool, chr, concat,
                                                 length, or, not)

import           Language.OutSystems.Lang
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
comma p = symbol "," >> p

--------------------------------------------------------------------------------
-- Operators

--------------------------------------------------------------------------------
-- Parser

newtype Parser' f a = Parser' { getParser :: Parser (f a) }
-- newtype Parser'' e s m f a = Parser'' { runParser'' :: ParsecT e s m (f a) }

-- fun name f args = Parser' $ string name *>
--   parens (f <$> sequenceA args)

instance LangText f => LangText (Parser' f) where
  int _ = Parser' $ int <$> lexeme L.decimal

  {- https://codereview.stackexchange.com/a/2572/141067
     I'll keep this link here just in case I need it later.
  -}
  text _ = let quote = char '\"' in Parser' $ text . T.pack <$>
    (quote >> manyTill latin1Char quote)

  length (Parser' parser) = Parser' $ string "Length" *>
    parens (length <$> parser)

  substr (Parser' p1) (Parser' p2) (Parser' p3) = Parser' $ string "Substr" *>
    parens (substr <$> p1 <*> comma p2 <*> comma p3)

  concat (Parser' p1) (Parser' p2) = Parser' $ string "Concat" *>
    parens (concat <$> p1 <*> comma p2)

  chr (Parser' p1) = Parser' $ string "Chr" *>
    parens (chr <$> p1)

  index0 (Parser' p1) (Parser' p2) = Parser' $ string "Index" *>
    parens (index0 <$> p1 <*> comma p2)

  index1 (Parser' p1) (Parser' p2) (Parser' p3) = Parser' $ string "Index" *>
    parens (index1 <$> p1 <*> comma p2 <*> comma p3)

  replace (Parser' p1) (Parser' p2) (Parser' p3) = Parser' $ string "Replace" *>
    parens (replace <$> p1 <*> comma p2 <*> comma p3)

  lower (Parser' p1) = Parser' $ string "Lower" *>
    parens (lower <$> p1)

  upper (Parser' p1) = Parser' $ string "Upper" *>
    parens (upper <$> p1)

  trimEnd (Parser' p1) = Parser' $ string "TrimEnd" *>
    parens (trimEnd <$> p1)

  trimStart (Parser' p1) = Parser' $ string "TrimStart" *>
    parens (trimStart <$> p1)

  trim (Parser' p1) = Parser' $ string "Trim" *>
    parens (trim <$> p1)

instance LangBool f => LangBool (Parser' f) where
  bool _ = Parser' $ bool <$> (true <|> false)
    where true  = True <$ symbol "True"
          false = False <$ symbol "False"

  if_ (Parser' p1) (Parser' p2) (Parser' p3) = Parser' $ string "If" *>
    parens (if_ <$> p1 <*> comma p2 <*> comma p3)

  or (Parser' p1) (Parser' p2) = Parser' $ string "or" *>
    parens (or <$> p1 <*> comma p2)

  not (Parser' p1) = Parser' $ string "not" *>
    parens (not <$> p1)
