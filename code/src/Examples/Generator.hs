{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE OverloadedStrings   #-}

{- |
Module:      Examples.Generator
Description: (Will, at some point) Generate I/O examples from OutSystems expressions
Copyright:   (c) Rodrigo Bernardo, 2018
License:     ???
Maintainer:  rodrigo.bernardo@tecnico.ulisboa.pt
Stability:   ??? Doesn't work yet
Portability: ???
-} 


module Examples.Generator where

import           Control.Applicative

import qualified Data.ByteString.Lazy.Char8     as BSL
import           Data.Text                      as T    ( Text )

import qualified Codec.Compression.GZip         as GZip
import           Data.Aeson                             ( FromJSON(..)
                                                        , Value(..)
                                                        , decode
                                                        , withObject
                                                        , (.:)
                                                        )


data Expression = Expression {
    exprText      :: Text
  , exprExprKey   :: Text
  , exprRefs      :: [Text]
  , exprType      :: Text
  , exprFunctions :: [Text]
  , exprOmlKey    :: Text
  } deriving (Show, Eq)

-- Generics don't seem to work here.
instance FromJSON Expression where
  parseJSON = withObject "Expression" $ \v -> Expression
    <$> v .: "text"
    <*> v .: "exprKey"
    <*> v .: "refs"
    <*> v .: "type"
    <*> v .: "functions"
    <*> v .: "omlKey"


-- | Decodes a compressed gzip file in jsonlines format.
decodeJSONLinesGZ :: FromJSON a => FilePath -> IO (Maybe [a])
decodeJSONLinesGZ file = do
    content <- GZip.decompress <$> BSL.readFile file
    return $ traverse decode $ BSL.lines content

