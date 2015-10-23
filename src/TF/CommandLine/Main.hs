{-# LANGUAGE RecordWildCards,DeriveDataTypeable #-}

module Main where


import Data.Data
-- import Control.Lens ((&))
import Lens.Simple
import System.Console.CmdArgs
import TF.CallChecker (checkFile)
import TF.Types hiding (def)

data Args = Args { fileName :: String
                 , localFailure :: Bool
                 , coreDynamic :: Bool
                 , forcedEffects :: Bool
                 , multipleEffects :: Bool
                 , casts :: Bool
                 , miniOOF :: Bool
                 , dynamicInStackComments :: Bool
                 } deriving (Show,Data,Typeable,Eq,Read)

arguments = Args { fileName = def
            , localFailure = def 
            , coreDynamic = def 
            , forcedEffects = def 
            , multipleEffects = def 
            , casts = def 
            , miniOOF = def 
            , dynamicInStackComments = def 
            } 

                            
main = do
  a@(Args{..}) <- cmdArgs arguments

  let config = ParseConfig {} & typeCheck                    .~ True
                              & topLevelEmpty                .~ True
                              & readFromStream               .~ True
                              & allowLocalFailure            .~ localFailure
                              & allCoreDynamic               .~ coreDynamic
                              & allowForcedEffects           .~ forcedEffects
                              & allowMultipleEffects         .~ multipleEffects
                              & thirdParty                   .~ []
                              & allowCasts                   .~ casts
                              & allowOOP                     .~ miniOOF
                              & allowDynamicInStackComments  .~ dynamicInStackComments
                              & subtypes                     .~ const []
  checkFile config fileName
