{-# LANGUAGE LambdaCase #-}
module Main where

import           Components
import           Constraints
import           Types

import           Control.Monad.Reader
import           Data.List
import           Data.Either
import           Data.Maybe
import           Data.SBV             hiding (name)
import           Data.SBV.Control

config0 = Config { examples = [ ([Left "John", Left "Doe"], Left "John Doe") ]
                 , library = [ concat_ , length_ , index_ ,  substr_]
                 -- , library = [replace_]
                 , constCount = 1
                 , componentCount = 2
                 }

config0' = Config { examples = [ ([Left "John", Left "Doe"], Left "John Doe")
                               , ([Left "Anne", Left "Joe"], Left "Anne Joe")
                               ]
                  , library = [ concat_ , length_ , index_ ,  substr_]
                  -- , library = [replace_]
                  , constCount = 1
                  , componentCount = 2
                  }

config1 = Config { examples = [ ([Left "John Michael Doe", Left "Dr. "], Left "Dr. John")
                              -- , ([Left "Anne Marie", Left "Dr. "], Left "Dr. Anne")
                              ]
                 , library = [concat_, length_, index_, substr_-- , replace_
                             ]
                 , constCount = 2
                 , componentCount = 3
                 }

config1' = Config { examples = [ ([Left "John Michael Doe", Left "Dr. "], Left "Dr. John")
                               , ([Left "Anne Marie", Left "Dr. "], Left "Dr. Anne")
                               ]
                  , library = [concat_, length_, index_, substr_-- , replace_
                              ]
                  , constCount = 2
                  , componentCount = 3
                  }

config2 = Config { examples = [ ([Left "abc", Left "b", Left "B"], Left "aBc") ]
                 , library = [replace_]
                 , constCount = 1
                 , componentCount = 1
                 }



main :: IO ()
main = do
  let cfg = config2

  runSMT $ do
    res <- runReaderT formula cfg
    query $ checkSat >>= \case
      Sat -> io . putStrLn =<< extractProgram cfg res
      x -> io $ print x

synth :: Config -> IO ()
synth cfg = runSMT $ runReaderT formula cfg >>= \res -> query $
  checkSat >> extractProgram cfg res >>= io . putStrLn


sat' :: Config -> IO SatResult
sat' config = sat $ void $ runReaderT formula config


ucore :: Config -> IO ()
ucore cfg = do mbCore <- runSMT $ do
                 setOption $ ProduceUnsatCores True
                 runReaderT formula cfg

                 query $ do cs <- checkSat
                            case cs of
                              Unsat -> Just <$> getUnsatCore
                              _     -> return Nothing

               case mbCore of
                 Nothing   -> putStrLn "Problem is satisfiable."
                 Just core -> putStrLn $ "Unsat core is: " ++ show core


extractProgram :: Config -> Result -> Query String
extractProgram cfg res = do
  let inputCount = length $ fst $ head $ examples cfg
      nameit pre x = pre <> show x

      inputNames = map (nameit "x") [0 .. inputCount - 1]
      constNames = map (nameit "c") [0 .. constCount cfg - 1]
      resNames   = map (nameit "r") [0 .. componentCount cfg - 1]

      line2name =
        zip [1 .. inputCount] inputNames <>
        zip [inputCount + 1 .. inputCount + constCount cfg] constNames <>
        zip [inputCount + constCount cfg + 1 ..] resNames

  consts <- map (either id show) <$> mapM getValue (resConsts res)
  comps <- map (name . ((library cfg !!) . subtract 1) . fromIntegral) <$>
           mapM getValue (resActivs res)
  locss <- map catMaybes <$> mapM (mapM getValue) (resLocations res)

  let topLine = "prog(" <> intercalate ", " inputNames <> "):"
  let constLines = zipWith (\c n -> n <> " = " <> show c) consts constNames
  let resLines = flip map (zip3 resNames comps locss) $ \(r, f, ls) ->
        let params = map (fromJust . flip lookup line2name . fromIntegral) ls
        in r <> " = " <> f <> "(" <> intercalate ", " params  <> ")"

  let indent n = map (replicate n ' ' <>)

  return $ unlines $ [topLine] <> indent 2 (constLines <> resLines)
