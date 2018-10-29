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

import qualified Codec.Compression.GZip         as GZip
import           Control.Applicative
import           Control.Monad                  ( mzero )
import           Data.Aeson                     ( FromJSON(..)
                                                , ToJSON(..)
                                                , Value(..)
                                                , decode
                                                , object
                                                , pairs
                                                , (.:)
                                                , (.:?)
                                                , (.=)
                                                )
import qualified Data.ByteString.Lazy.Char8     as BSL
import           Data.Maybe
import           Data.Monoid
import           Data.Text                      as T ( Text )
import           Data.Text.Encoding             as T
import GHC.Generics


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
    

