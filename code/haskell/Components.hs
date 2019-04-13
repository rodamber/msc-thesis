{-# LANGUAGE TypeApplications #-}
module Components where

import           Control.Monad

import           Data.SBV                  hiding (name)
import qualified Data.SBV.Maybe            as SBV
import           Data.SBV.String           ((.++))
import qualified Data.SBV.String           as SBV
import           Data.SBV.Tools.BoundedFix (bfix)

import           Types


-- Get n formal parameters and set the rest to none
getFormals :: Integral a => a -> [SMaybe Sort] -> [SSort -> SBool]
           -> (SBool, [SSort])
getFormals n xs istypes = let (ys, zs) = splitAt (fromIntegral n) xs
                              ys' = map SBV.fromJust ys
                              c = sAll SBV.isJust ys .&&
                                  sAll SBV.isNothing zs .&&
                                  foldr (.&&) sTrue (zipWith ($) istypes ys')
                          in (c, ys')

-- -----------------------------------------------------------------------------
--                                 Components
-- -----------------------------------------------------------------------------

mkComponent :: String -> Int8 -> [SSort -> SBool]
            -> ([SSort] -> SSort -> SBool) -> Component
mkComponent name arity istypes run =
  Component { name = name,
              arity = arity,
              run = \xs r -> let (c, xs') = getFormals arity xs istypes
                             in c .&& run xs' r
            }

concat_ :: Component
concat_ = mkComponent "Concat" 2 [isSString, isSString] $
  \[x1, x2] r -> embed (SBV.concat (proj x1) (proj x2)) .== r


index_ :: Component
index_ = mkComponent "Index" 3 [isSString, isSString, isSInt] $
  \[x1, x2, x3] r ->
    embed (SBV.offsetIndexOf (proj x1) (proj x2) (proj x3)) .== r


substr_ :: Component
substr_ = mkComponent "Substr" 3 [isSString, isSInt, isSInt] $
  \[x1, x2, x3] r -> embed (SBV.subStr (proj x1) (proj x2) (proj x3)) .== r


length_ :: Component
length_ = mkComponent "Length" 1 [isSString] $
  \[x1] r -> embed (SBV.length (proj x1)) .== r


replace_ :: Component
replace_ = mkComponent "Replace" 3 [isSString, isSString, isSString] $
  \[x1, x2, x3] r -> embed (replaceAll (proj x1) (proj x2) (proj x3)) .== r


replaceAll :: SString -> SString -> SString -> SString
replaceAll s old new = ite (SBV.null s) s $ ite (SBV.null old) s $
                       bfix 10 "replaceAll" replaceAll' s ""
  where
    len = SBV.length old
    replaceAll' f s acc = let ix = SBV.indexOf s old
                              left = SBV.take ix s
                              right = SBV.drop (ix + len) s
                          in ite (ix .== -1) (acc .++ s)
                             (f right (acc .++ left .++ new))


idS_ :: Component
idS_  = mkComponent "Id" 1 [\x -> isSString x] $
  \[x1] r -> embed @SString (proj x1) .== r

--------------------------------------------------------------------------------
--                                   Utils
--------------------------------------------------------------------------------

-- bfix' :: SymVal a => Int -> String -> ((SBV a -> r) -> (SBV a -> r)) -> SBV a -> r
-- bfix' bound nm f x
--   | isConcrete x = g x
--   | True         = unroll bound x
--   where g        = f g
--         unroll 0 = uninterpret nm
--         unroll i = f (unroll (i-1))
