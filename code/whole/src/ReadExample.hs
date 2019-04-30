{-# LANGUAGE DeriveGeneric #-}
module ReadExample
  ( readExamplesFromFile
  , readExamples
  ) where

import           Control.Arrow ((&&&))
import           GHC.Generics

import           Data.Aeson
import qualified Data.ByteString.Lazy as B

import           Types


data ExampleRecord =
  ExampleRec { inputs :: [Sort], output :: Sort }
  deriving (Generic, Show)

instance FromJSON ExampleRecord


newtype ExampleListRecord =
  ExampleListRec { examples :: [ExampleRecord] }
  deriving (Generic, Show)

instance FromJSON ExampleListRecord


toExamples :: ExampleListRecord -> [Example]
toExamples = map (inputs &&& output) . examples


readExamples :: B.ByteString -> [Example]
readExamples x = either error toExamples (eitherDecode x)


readExamplesFromFile :: FilePath -> IO [Example]
readExamplesFromFile f = either error toExamples <$> eitherDecodeFileStrict f
