{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module Examples.Parser where

import           Control.Applicative
import           Control.Monad                  ( forM_
                                                , join
                                                , mzero
                                                )
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
import           System.Environment             ( getArgs )
import           System.Exit                    ( exitFailure
                                                , exitSuccess
                                                )
import           System.IO                      ( hPutStrLn
                                                , stderr
                                                )

-- | Workaround for https://github.com/bos/aeson/issues/287.
--o .:?? val = fmap join (o .:? val)


data TopLevel = TopLevel {
    topLevelText      :: Text,
    topLevelExprKey   :: Text,
    topLevelRefs      :: [Text],
    topLevelType      :: Text,
    topLevelFunctions :: [Text],
    topLevelOmlKey    :: Text
  } deriving (Show, Eq)


instance FromJSON TopLevel where
  parseJSON (Object v) = TopLevel <$>
        v .:   "text"
    <*> v .:   "exprKey"
    <*> v .:   "refs"
    <*> v .:   "type"
    <*> v .:   "functions"
    <*> v .:   "omlKey"
  parseJSON _          = mzero


instance ToJSON TopLevel where
  toJSON     TopLevel {..} = object [
      "text"      .= topLevelText
    , "exprKey"   .= topLevelExprKey
    , "refs"      .= topLevelRefs
    , "type"      .= topLevelType
    , "functions" .= topLevelFunctions
    , "omlKey"    .= topLevelOmlKey
    ]
  toEncoding TopLevel {..} = pairs (
      "text"      .= topLevelText      <>
      "exprKey"   .= topLevelExprKey   <>
      "refs"      .= topLevelRefs      <>
      "type"      .= topLevelType      <>
      "functions" .= topLevelFunctions <>
      "omlKey"    .= topLevelOmlKey
    )


parse :: FilePath -> IO TopLevel
parse filename = do
  input <- BSL.readFile filename
  case decode input of
    Nothing -> fatal $ case (decode input :: Maybe Value) of
      Nothing -> "Invalid JSON file: " ++ filename
      Just _  -> "Mismatched JSON value from file: " ++ filename
    Just r -> return (r :: TopLevel)
 where
  fatal :: String -> IO a
  fatal msg = do
    hPutStrLn stderr msg
    exitFailure

main :: IO ()
main = do
  filenames <- getArgs
  forM_ filenames $ \f -> do
    p <- parse f
    p `seq` putStrLn $ "Successfully parsed " ++ f
  exitSuccess
