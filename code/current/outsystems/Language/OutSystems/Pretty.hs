module Language.OutSystems.Pretty where

import Relude

import Language.OutSystems.Cast
import Language.OutSystems.Lang (Lang0(..))


-- * Pretty Printer ----------------------------------------------------------

newtype Pretty a = Pretty { pretty :: Text }


instance Lang0 Pretty where
  intL x          = Pretty $ show x
  textL x         = Pretty $ show x
  lengthL x       = Pretty $ "Length(" <> pretty x <> ")"
  substrL x y z w = Pretty $ "Substr(" <> pretty x <> ","
                                       <> pretty y <> ","
                                       <> pretty z <> ","
                                       <> pretty w <> ")"
  trimL x         = Pretty $ "Trim(" <> pretty x <> ")"
  replaceL x y z  = Pretty $ "Replace(" <> pretty x <> ","
                                        <> pretty y <> ","
                                        <> pretty z <> ")"
