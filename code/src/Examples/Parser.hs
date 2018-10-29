{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE OverloadedStrings   #-}

{- |
Module:      Examples.Parser
Description: (Will, at some point) Generate I/O examples from OutSystems expressions
Copyright:   (c) Rodrigo Bernardo, 2018
License:     ???
Maintainer:  rodrigo.bernardo@tecnico.ulisboa.pt
Stability:   ??? Doesn't work yet
Portability: ???
-} 


module Examples.Parser where

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
import qualified Data.ByteString.Lazy.Char8    as BSL
import           Data.Monoid
import           Data.Text                      ( Text )

import GHC.Generics

data Expression = Expression {
    exprText      :: Text
  , exprExprKey   :: Text
  , exprRefs      :: [Text]
  , exprType      :: Text
  , exprFunctions :: [Text]
  , exprOmlKey    :: Text
  } deriving (Show, Eq, Generic)

