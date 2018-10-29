{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}

module Examples.Parser where

import           Control.Applicative
import           Control.Monad                  ( forM_
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


data Expression = Expression {
    exprText      :: Text
  , exprExprKey   :: Text
  , exprRefs      :: [Text]
  , exprType      :: Text
  , exprFunctions :: [Text]
  , exprOmlKey    :: Text
  } deriving (Show, Eq)


instance FromJSON Expression where
  parseJSON (Object v) = Expression <$>
        v .:   "text"
    <*> v .:   "exprKey"
    <*> v .:   "refs"
    <*> v .:   "type"
    <*> v .:   "functions"
    <*> v .:   "omlKey"

  parseJSON _          = mzero


instance ToJSON Expression where
  toJSON     Expression {..} = object [
      "text"      .= exprText
    , "exprKey"   .= exprExprKey
    , "refs"      .= exprRefs
    , "type"      .= exprType
    , "functions" .= exprFunctions
    , "omlKey"    .= exprOmlKey
    ]

  toEncoding Expression {..} = pairs (
      "text"      .= exprText      <>
      "exprKey"   .= exprExprKey   <>
      "refs"      .= exprRefs      <>
      "type"      .= exprType      <>
      "functions" .= exprFunctions <>
      "omlKey"    .= exprOmlKey
    )


parse :: FilePath -> IO Expression
parse filename = do
  input <- BSL.readFile filename
  case decode input of
    Nothing -> fatal $ case (decode input :: Maybe Value) of
      Nothing -> "Invalid JSON file: " ++ filename
      Just _  -> "Mismatched JSON value from file: " ++ filename
    Just r -> return (r :: Expression)
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
