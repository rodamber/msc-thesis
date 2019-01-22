{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
module Language.OutSystems.Serialize where

import           Relude
import qualified Relude.Unsafe as Unsafe

import qualified Data.Text                as T
import           Data.Tree
import           Data.Typeable

import           Language.OutSystems.Cast
import           Language.OutSystems.Lang (Lang0 (..))

{- Questions 
1. Is there any way to make this structure extensible in the same way that the
  language is?
2. If so, is it possible to create an extensible parser out of the first one?
   (This should be easy right? Isn't this what parser combinators are all about?)
-}

-- * Serialize -----------------------------------------------------------------

newtype Serialize a = S { toTree :: Tree Text }

instance Lang0 Serialize where
  intL x                          = S $ Node (show x) []
  textL x                         = S $ Node (show x) []
  lengthL (S x)                   = S $ Node "Length" [x]
  substrL (S x) (S y) (S z) (S w) = S $ Node "Substr" [x, y, z, w]
  trimL (S x)                     = S $ Node "Trim"   [x]
  replaceL (S x) (S y) (S z)      = S $ Node "Substr" [x, y, z]


-- * Deserialize ---------------------------------------------------------------
-- ** Types --------------------------------------------------------------------

class Types0 f where
  intT  :: f Int
  textT :: f Text


newtype Ty0 a = Ty0 { unTy :: forall f. Types0 f => f a }


instance Types0 Ty0 where
  intT  = Ty0 intT
  textT = Ty0 textT


-- ** Type Safe Casting --------------------------------------------------------

instance Typeable a => Types0 (Cast a) where
  intT  = Proof eqT
  textT = Proof eqT


-- ** Dynamic Typing -----------------------------------------------------------

data Dynamic0 f = forall a. Dynamic0 (Ty0 a) (f a)

fromDynamic0 :: Types0 (Cast a) => Dynamic0 f -> Maybe (f a)
fromDynamic0 = \case Dynamic0 (Ty0 ty) f -> as ty f


-- ** Deserialization ----------------------------------------------------------

fromTree :: (Typeable a, Lang0 f) => Tree Text -> Maybe (f a)
fromTree = fromTree' >=> fromDynamic0

fromTree' :: Lang0 f => Tree Text -> Maybe (Dynamic0 f)
fromTree' (Node x ys) = case readMaybe (T.unpack x) of
  Just (z :: Int) -> pure $ Dynamic0 (Ty0 intT) (intL z)
  Nothing -> case readMaybe (T.unpack x) of
    Just (z :: Text) -> pure $ Dynamic0 (Ty0 textT) (textL z)
    Nothing -> case x of
      "Length" -> do
        let [x] = ys
        f <- fromTree'' x
        pure $ Dynamic0 (Ty0 intT) (lengthL f)
      "Substr" -> do
        let [x, y, z, w] = ys
        f <- fromTree'' x
        g <- fromTree'' y
        h <- fromTree'' z
        j <- fromTree'' w
        pure $ Dynamic0 (Ty0 textT) (substrL f g h j)
      "Trim" -> do
        let [x] = ys
        f <- fromTree'' x
        pure $ Dynamic0 (Ty0 textT) (trimL f)
      "replaceL" -> do
        let [x, y, z] = ys
        f <- fromTree'' x
        g <- fromTree'' y
        h <- fromTree'' z
        pure $ Dynamic0 (Ty0 textT) (replaceL f g h)


fromTree'' :: (Lang0 f, Typeable a) => Tree Text -> Maybe (f a)
fromTree'' x = do
  Dynamic0 (Ty0 ty) f <- fromTree' x
  as ty f
