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
import           Data.Maybe                             ( fromJust )
import           GHC.Generics

import qualified Data.ByteString.Lazy.Char8     as BSL
import           Data.Text                      as T    ( Text )

import qualified Codec.Compression.GZip         as GZip
import           Data.Aeson                             ( FromJSON(..), decode )


data Expression = Expression {
    exprText      :: Text
  , exprExprKey   :: Text
  , exprRefs      :: [Text]
  , exprType      :: Text
  , exprFunctions :: [Text]
  , exprOmlKey    :: Text
  } deriving (Show, Eq, Generic)

instance FromJSON Expression


readExpressionsGZ :: FilePath -> IO [Expression]
readExpressionsGZ file = do 
    content <- GZip.decompress <$> BSL.readFile file
    return $ fromJust . decode <$> BSL.lines content
    

