{-# LANGUAGE DeriveGeneric #-}

module OutSystems where

import Prelude

import Data.Aeson -- (FromJSON (..), withObject, (.:), decode)
import qualified Data.ByteString.Lazy.Char8 as LBS8

data Functions
  -- Data Conversion
  = BooleanToInteger          | BooleanToText             | DateTimeToDate
  | DateTimeToText            | DateTimeToTime            | DateToDateTime
  | DateToText                | DecimalToBoolean          | DecimalToInteger
  | DecimalToIntegerValidate  | DecimalToLongInteger      | DecimalToLongIntegerValidate
  | DecimalToText             | LongIntegerToInteger      | LongIntegerToIntegerValidate
  | LongIntegerToIdentifier   | LongIntegerToText         | IdentifierToInteger
  | IdentifierToLongInteger   | IdentifierToText          | IntegerToBoolean
  | IntegerToDecimal          | IntegerToIdentifier       | IntegerToText
  | NullDate                  | NullIdentifier            | NullObject
  | NullBinary                | NullTextIdentifier        | TextToDate
  | TextToDateTime            | TextToDateTimeValidate    | TextToDateValidate
  | TextToDecimal             | TextToDecimalValidate     | TextToIdentifier
  | TextToInteger             | TextToLongInteger         | TextToIntegerValidate
  | TextToLongIntegerValidate | TextToTime                | TextToTimeValidate
  | TimeToText                | ToObject
  -- Date and Time
  | AddDays                   | AddHours                  | AddMinutes
  | AddMonths                 | AddSeconds                | AddYears
  | BuildDateTime             | CurrDate                  | CurrDateTime
  | CurrTime                  | Day                       | DayOfWeek
  | DiffDays                  | DiffHours                 | DiffMinutes
  | DiffSeconds               | Hour                      | Minute
  | Month                     | NewDate                   | NewDateTime
  | NewTime                   | Second                    | Year
  -- Email
  | EmailAddressCreate        | EmailAddressesConcatenate | EmailAddressValidate
  -- Environment
  | GetApplicationServerType  | GetCurrentLocale          | GetDatabaseProvider
  | GetUserAgent              | GetOwnerEspaceIdentifier  | GetEntryEspaceName
  | GetEntryEspaceId          | GetObsoleteTenantId
  -- Format
  | FormatDecimal             | FormatPercent             | FormatPhoneNumber
  | FormatText                | FormatDateTime
  -- Math
  | Abs                       | Mod                       | Power
  | Round                     | Sqrt                      | Trunc
  -- Misc
  | GeneratePassword          | If                        | IsLoadingScreen
  | CurrentThemeIsMobile
  -- Numeric
  | Max                       | Min                       | Sign
  -- Roles
  | CheckRole                 | GetUserId
  -- Text
  | Chr                       | Concat                    | EncodeHtml
  | EncodeJavaScript          | EncodeSql                 | EncodeUrl
  | Index                     | Length                    | NewLine
  | Replace                   | Substr                    | ToLower
  | ToUpper                   | Trim                      | TrimEnd
  | TrimStart
  -- URL
  | AddPersonalAreaToURLPath  | GetBookmarkableURL        | GetPersonalAreaName
  | GetOwnerURLPath           | GetExceptionURL
  deriving (Show, Read, Eq, Ord, Generic)

instance FromJSON Functions

data Types
  = BinaryData | Boolean | Currency | Date | Time | DateTime | Integer
  | LongInteger | Decimal | Email | PhoneNumber | Text | Identifier
  deriving (Show, Read, Eq, Ord, Generic)

instance FromJSON Types

data Expression = Expression
  { text  :: Text
  , type_ :: Types
  , funs  :: [Functions]
  } deriving (Show, Read, Eq, Ord)

instance FromJSON Expression where
  parseJSON = withObject "Expression" $ \v -> Expression
    <$> v .: "text"
    <*> v .: "type"
    <*> v .: "functions"

readJsonlines :: FilePath -> IO [LByteString]
readJsonlines fp = LBS8.lines <$> LBS8.readFile fp

expressions :: FilePath -> IO [Expression]
expressions fp = ordNub . mapMaybe decode <$> readJsonlines fp

