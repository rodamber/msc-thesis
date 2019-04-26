{-# LANGUAGE TypeApplications #-}
module Components
  ( concat_
  , length_
  , replace_
  , substr_
  , tolower_
  , toupper_
  , trim_
  , trim_start_
  , trim_end_
  , add_
  , sub_
  ) where

import           Data.SBV                  hiding (name, output)
import qualified Data.SBV.Maybe            as SBV
import           Data.SBV.String           ((.++), (.:))
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


length_ :: Component
length_ = mkComponent "Length" 1 [isSString] $
  \[x1] r -> embed (SBV.length (proj x1)) .== r


replace_ :: Component
replace_ = mkComponent "Replace" 3 [isSString, isSString, isSString] $
  \[x1, x2, x3] r -> embed (replaceAll (proj x1) (proj x2) (proj x3)) .== r


replaceAll :: SString -> SString -> SString -> SString
replaceAll s old new = ite (SBV.null s) s $ ite (SBV.null old) s $
                       bfix 10 "replaceAll" replaceAll' s (literal "")
  where
    len = SBV.length old
    replaceAll' f s acc = let ix = SBV.indexOf s old
                              left = SBV.take ix s
                              right = SBV.drop (ix + len) s
                          in ite (ix .== -1) (acc .++ s)
                             (f right (acc .++ left .++ new))


substr_ :: Component
substr_ = mkComponent "Substr" 3 [isSString, isSInt, isSInt] $
  \[x1, x2, x3] r -> embed (SBV.subStr (proj x1) (proj x2) (proj x3)) .== r


tolower_ :: Component
tolower_ = mkComponent "ToLower" 1 [isSString] $
  \[x1] r -> embed (map_str (caseit lowermap) (proj x1)) .== r


toupper_ :: Component
toupper_ = mkComponent "ToUpper" 1 [isSString] $
  \[x1] r -> embed (map_str (caseit uppermap) (proj x1)) .== r


map_str :: (SChar -> SChar) -> SString -> SString
map_str f s = bfix 10 "map_str" open s where
  open g s = ite (SBV.null s) SBV.nil $
             SBV.singleton (f $ SBV.head s) .++ g (SBV.tail s)


lowermap :: [(SChar, SChar)]
lowermap = zip (map literal ['A' .. 'Z']) (map literal ['a' .. 'z'])


uppermap :: [(SChar, SChar)]
uppermap = zip (map literal ['a' .. 'z']) (map literal ['A' .. 'Z'])


caseit :: [(SChar, SChar)] -> SChar -> SChar
caseit m c = foldr (\(u,l) z -> ite (c .== u) l z) c m


trim_ :: Component
trim_ = mkComponent "Trim" 1 [isSString] $
  \[x1] r -> embed (trimLR (proj x1)) .== r


trim_start_ :: Component
trim_start_ = mkComponent "TrimStart" 1 [isSString] $
  \[x1] r -> embed (trimL (proj x1)) .== r


trim_end_ :: Component
trim_end_ = mkComponent "TrimEnd" 1 [isSString] $
  \[x1] r -> embed (trimR (proj x1)) .== r


trimLR :: SString -> SString
trimLR = trimR . trimL


trimL :: SString -> SString
trimL = bfix 10 "trimL" open where
  open f s = ite (SBV.head s .== literal ' ') (f $ SBV.tail s) s


trimR :: SString -> SString
trimR = srev . trimL . srev


-- symbolic string reverse
srev :: SString -> SString
srev s = bfix 10 "srev" open s SBV.nil where
  open f s acc = ite (SBV.null s) acc $
    f (SBV.tail s) (SBV.head s .: acc)


add_ :: Component
add_ = mkComponent "Add" 2 [isSInt, isSInt] $
  \[x1, x2] r -> embed @SInteger (proj x1 + proj x2) .== r

sub_ :: Component
sub_ = mkComponent "Sub" 2 [isSInt, isSInt] $
  \[x1, x2] r -> embed @SInteger (proj x1 - proj x2) .== r

