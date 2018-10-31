{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Examples.Expressions where

import           Data.Text as T (Text)


textFuns :: [Text]
textFuns =  ["Chr", "Concat", "Index", "Length", "NewLine", "Replace", "Substr",
  "ToLower", "ToUpper", "Trim", "TrimEnd", "TrimStart"]
  -- Missing: "EncodeHtml", "EncodeJavaScript", "EncodeSql", "EncodeUrl",

