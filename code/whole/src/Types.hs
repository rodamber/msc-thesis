{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Types
  ( Sort
  , SSort
  , Example
  , showExample
  , Act
  , Loc
  , SLoc
  , Component(..)
  , Library
  , isSString
  , isSInt
  , Embedding(..)
  , Projection(..)
  )
  where

import           Data.SBV
import qualified Data.SBV.Either as SBV

-- TODO Check if something other than Integer makes it faster
type Sort = Either String Integer
type SSort = SEither String Integer

type Example = ([Sort], Sort)

data Showable = forall a . Show a => Showable a

instance Show Showable where
  show (Showable x) = show x

showExample :: Example -> String
showExample (xs, y) = show (map showSort xs, showSort y)

showSort :: Sort -> Showable
showSort = either Showable Showable

type Act = Int8
type Loc = Int8
type SLoc = SBV Loc

data Component = Component
  { name  :: String
  , arity :: Int8
  , run   :: [SMaybe Sort] -> SSort -> SBool
  }

type Library = [Component]

isSString :: SSort -> SBool
isSString = SBV.isLeft

isSInt :: SSort -> SBool
isSInt = SBV.isRight

class Embedding a           where embed :: a -> SSort
instance Embedding SString  where embed =  SBV.sLeft
instance Embedding SInteger where embed =  SBV.sRight

class Projection a           where proj :: SSort -> a
instance Projection SString  where proj = SBV.fromLeft
instance Projection SInteger where proj = SBV.fromRight

