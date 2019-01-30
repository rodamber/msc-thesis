{-# LANGUAGE TypeOperators #-}

module Language.OutSystems.Cast where

import Relude

import Data.Type.Equality

-- * Safe Type Casting ---------------------------------------------------------

newtype Cast a b = Proof (Maybe (a :~: b))

as :: Cast a b -> c b -> Maybe (c a)
as (Proof (Just equ)) f = Just $ castWith (apply Refl $ sym equ) f
as _                  _ = Nothing


