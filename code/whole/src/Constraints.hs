{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications           #-}
module Constraints where

import           Control.Monad
import           Control.Monad.Reader
import           Data.List            (genericLength, maximumBy, zip4)
import           Data.Maybe
import           Data.Ord             (comparing)

import           Data.SBV
import qualified Data.SBV             as SBV
import qualified Data.SBV.Either      as SBV
import           Data.SBV.Internals   (SolverContext)
import qualified Data.SBV.Maybe       as SBV
import qualified Data.SBV.String      as SBV
import           Data.SBV.Tuple       ((^.), _1)
import qualified Data.SBV.Tuple       as SBV

import           Components
import           Types


data Config = Config
  { examples       :: [Example]
  , library        :: Library
  , constCount     :: Int
  , componentCount :: Int
  }


data Env = Env
  { components :: Library
  , activs     :: [SInt8]
  , inputs     :: [(SLoc, SSort)]
  , output     :: SSort
  , consts     :: [(SLoc, SSort)]
  , retVals    :: [(SLoc, SSort)]
  , formals    :: [[SMaybe Sort]]
  , locations  :: [[SMaybe Loc]] -- ^ locations for formal parameters
  }


data Result = Result
  { resActivs    :: [SInt8]
  , resConsts    :: [SSort]
  , resLocations :: [[SMaybe Loc]]
  }


type ConstraintGen env a = ReaderT env Symbolic a


mkActivs :: ConstraintGen Config [SInt8]
mkActivs = do
  fno <- reader componentCount
  lib <- reader library
  acts <- lift $ mapM (\x -> sInt8 ("activ_" <> show x)) [1 .. fno]

  forM_ acts $ \a -> lift $ do
    constrain $ a .>= 1
    constrain $ a .<= literal (genericLength lib)

  return acts


mkInputss :: ConstraintGen Config [[(SLoc, SSort)]]
mkInputss = do
  inputss <- reader (map fst . examples)
  let sinputss = map (map literal) inputss
  return $ map (zip (map literal [1..])) sinputss


mkOutputs :: ConstraintGen Config [SSort]
mkOutputs = do -- map (literal . snd) <$> reader examples
  outputs <- reader (map snd . examples)
  return $ map literal outputs


mkConsts :: Int -> ConstraintGen Config [(SLoc, SSort)]
mkConsts inputCount = do
  constCount <- reader constCount

  forM [1 .. constCount] $ \i -> do
    let loc = literal $ fromIntegral $ inputCount + i
    x <- lift $ exists ("const_" <> show i)
    return (loc, x)


mkRetValss :: Int -> ConstraintGen Config [[(SLoc, SSort)]]
mkRetValss inputCount = do
  constCount <- reader constCount
  compCount <- reader componentCount
  outputs <- reader (map snd . examples)

  forM outputs $ \o -> lift $ do
    retVals <- forM [1 .. compCount] $ \n -> do
      let loc = literal $ fromIntegral $ inputCount + constCount + n
      x <- exists ("return_value_" <> show n)
      return (loc, x)

    constrain $ snd (last retVals) .== literal o
    return retVals


mkFormalss :: Int -> Int -> ConstraintGen Config [[[SMaybe Sort]]]
mkFormalss inputCount maxArity = do
  compCount <- reader componentCount
  examples <- reader examples

  forM examples $ \_ -> do
    forM [1 .. compCount] $ \i -> do
      forM [1 .. maxArity] $ \j -> lift $ do
        exists ("formal_" <> show i <> "_" <> show j)


mkLocations :: Int -> Int -> ConstraintGen Config [[SMaybe Loc]]
mkLocations inputCount maxArity = do
  compCount <- reader componentCount
  constCount <- reader constCount

  forM [1 .. compCount] $ \i -> do
    forM [1 .. maxArity] $ \j -> lift $ do

      loc <- exists ("loc_" <> show i <> "_" <> show j)
      let upperBound = (fromIntegral (inputCount + constCount + i))

      constrain $ SBV.isJust loc .=> SBV.fromJust loc .>= 1
      constrain $ SBV.isJust loc .=> SBV.fromJust loc .< literal upperBound

      return loc

flow :: ConstraintGen Env ()
flow = do
  inputs <- reader inputs
  consts <- reader consts
  retVals <- reader retVals

  forM_ (inputs <> consts <> retVals) $ \(xloc, x) -> do
    formals <- reader (concat . formals)
    locations <- reader (concat . locations)

    forM (zip locations formals) $ \(mloc, mp) -> lift $ do
      let loc = SBV.fromJust mloc
      let p = SBV.fromJust mp

      constrain $ SBV.isNothing mloc .<=> SBV.isNothing mp
      constrain $ SBV.isJust mloc .=> (loc .== xloc .=> p .== x)


allInputs :: ConstraintGen Env ()
allInputs = do
  inputs <- reader inputs
  locations <- reader (concat . locations)

  forM_ inputs $ \(iloc, _) -> lift $ do
    let clauses = map (\loc -> SBV.isJust loc .&& SBV.fromJust loc .== iloc)
                      locations
    constrain $ pbAtLeast clauses 1 -- TODO softConstraint?


allRetVals :: ConstraintGen Env ()
allRetVals = do
  retVals <- reader (init . retVals)

  forM_ (zip [1..] retVals) $ \(n, (rloc, _)) -> do
    locations <- reader (concat . drop n . locations)
    let clauses = map (\loc -> SBV.isJust loc .&& SBV.fromJust loc .== rloc)
                      locations
    lift $ constrain $ pbAtLeast clauses 1 -- TODO softConstraint?


spec :: ConstraintGen Env ()
spec = do
  activs <- reader activs
  formals <- reader formals
  retVals <- reader (map snd . retVals)
  lib <- reader components

  forM_ (zip4 activs formals retVals [1..]) $ \(a, params, r, j) ->
    forM_ (zip [1..] lib) $ \(i, component) -> lift $ do
      constrain $ a .== i .=> run component params r


prog :: ConstraintGen Env ()
prog = do
  flow
  allInputs
  allRetVals
  spec


formula :: ConstraintGen Config Result
formula = do
  inputCount <- reader (length . fst . head . examples)
  components <- reader library

  let maxArity = fromIntegral . maximum . (map arity) $ components

  activs <- mkActivs
  inputss <- mkInputss
  outputs <- mkOutputs
  consts <- mkConsts inputCount
  locations <- mkLocations inputCount maxArity

  retValss <- mkRetValss inputCount
  formalss <- mkFormalss inputCount maxArity

  forM_ (zip4 inputss outputs retValss formalss) $
    \(is, o, rs, fs) -> do
      let env = Env components activs is o consts rs fs locations
      lift $ runReaderT prog env

  return $ Result activs (map snd consts) locations
