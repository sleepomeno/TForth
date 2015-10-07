{-# LANGUAGE CPP#-}
module TF.Paths (getStaticDir) where

import Control.Monad
import System.FilePath

import qualified Paths_TypedForth (getDataDir)

#if CABAL
-- using cabal
import qualified Paths_TypedForth (getDataDir)

getStaticDir :: IO FilePath
getStaticDir = (</> "data") `liftM` Paths_TypedForth.getDataDir



#else
-- using GHCi

getStaticDir :: IO FilePath
getStaticDir = return "data/"

#endif

