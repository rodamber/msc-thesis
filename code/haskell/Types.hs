{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Types where

import           Data.SBV
import qualified Data.SBV.Either as SBV
import qualified Data.SBV.Maybe  as SBV

-- TODO Check if something other than Integer makes it faster
type Sort = Either String Integer
type SSort = SEither String Integer

type Example = ([Sort], Sort)

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

