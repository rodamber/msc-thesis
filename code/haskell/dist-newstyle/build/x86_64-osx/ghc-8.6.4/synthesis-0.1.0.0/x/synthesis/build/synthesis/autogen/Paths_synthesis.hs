{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_synthesis (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/Users/rodamber/.cabal/bin"
libdir     = "/Users/rodamber/.cabal/lib/x86_64-osx-ghc-8.6.4/synthesis-0.1.0.0-inplace-synthesis"
dynlibdir  = "/Users/rodamber/.cabal/lib/x86_64-osx-ghc-8.6.4"
datadir    = "/Users/rodamber/.cabal/share/x86_64-osx-ghc-8.6.4/synthesis-0.1.0.0"
libexecdir = "/Users/rodamber/.cabal/libexec/x86_64-osx-ghc-8.6.4/synthesis-0.1.0.0"
sysconfdir = "/Users/rodamber/.cabal/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "synthesis_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "synthesis_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "synthesis_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "synthesis_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "synthesis_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "synthesis_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
