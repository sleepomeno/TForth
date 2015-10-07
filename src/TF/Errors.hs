{-# LANGUAGE OverloadedStrings, StandaloneDeriving, TypeFamilies, DeriveFunctor, GADTs, TemplateHaskell, FunctionalDependencies, FlexibleInstances, GADTs, NoMonomorphismRestriction, DeriveGeneric,DeriveDataTypeable, DataKinds #-}
module TF.Errors where

import  Control.Lens
import           Data.Data hiding (DataType)
import           Control.Monad.Trans.Free
import           Control.Monad.State
import           Control.Monad.Writer
import           Control.Monad.Reader
import Text.PrettyPrint (Doc)
import GHC.Generics (Generic)
import Lens.Family.Total hiding ((&))
import           Control.Monad.RWS
-- import  Text.PrettyPrint (render)
import Data.Tree
import           Control.Error as E
import           Text.Parsec hiding (runParser, char)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as Te

import Data.Profunctor

import TF.ForthTypes

data MultiEffClash = IfElseExprNotStatic String String | IfExprNotStatic | MultiEffs String  deriving (Show, Read, Data, Typeable, Eq)
makeClassyPrisms ''MultiEffClash

data TypeClash = NotMatchingStackComment String | Clash String | TypeClashM MultiEffClash | ClashInWord String | UnemptyStack String String | BeginUntilNoFlag String deriving (Show, Read, Data, Typeable, Eq)
makeClassyPrisms ''TypeClash

data ParseErr = ParseErr' String | NotSameStreamArgs String deriving (Show, Typeable)
makeClassyPrisms ''ParseErr

data BuildWordErr = BuildWordErrP ParseErr deriving Show
makeClassyPrisms ''BuildWordErr

data OOPErr = DefinedTwice String | RedefinedField String | OOPErrT TypeClash | MethodNotSubtypeOfSuperclassMethod | TopConsumingMustBeClassType deriving Show
makeClassyPrisms ''OOPErr

data StreamArgErr = NumberAsStreamArg | MultiHigherOrderArg | HOTNotSubtype | StreamArgHasExecAndCompEffect deriving Show
makeClassyPrisms ''StreamArgErr

data AssertErr = MalformedAssert String | MultipleEffects deriving Show
makeClassyPrisms ''AssertErr

data ExecuteErr = ExecuteErrAssert AssertErr deriving Show
makeClassyPrisms ''ExecuteErr

data TickErr = TickErrAssert AssertErr deriving Show
makeClassyPrisms ''TickErr

data FeatureErr = CastsNotAllowed | OOPNotAllowed | ForcedEffectsNotAllowed deriving Show
makeClassyPrisms ''FeatureErr


data Error' = ErrorT TypeClash 
            | ErrorP ParseErr 
            | Impossible String 
            | ErrorW BuildWordErr 
            | ErrorO OOPErr 
            | DifferentChangeStates
            | ErrorS StreamArgErr
            -- | MalformedAssert String
            | ErrorTick TickErr
            | ErrorA AssertErr
            | ErrorE ExecuteErr
            | ErrorF FeatureErr
            | UnknownWord String
            deriving Show
makeClassyPrisms ''Error'


instance AsFeatureErr Error' where
  _FeatureErr = _ErrorF . _FeatureErr

instance AsMultiEffClash Error' where
  _MultiEffClash = _TypeClashM . _MultiEffClash
  
instance AsMultiEffClash TypeClash where
  _MultiEffClash = _TypeClashM . _MultiEffClash
  
instance AsAssertErr ExecuteErr where
  _AssertErr = _ExecuteErrAssert . _AssertErr

instance AsExecuteErr Error' where
  _ExecuteErr = _ErrorE . _ExecuteErr

instance AsAssertErr Error' where
  _AssertErr = _ErrorA . _AssertErr

instance AsAssertErr TickErr where
  _AssertErr = _TickErrAssert . _AssertErr

instance AsTickErr Error' where
  _TickErr = _ErrorTick . _TickErr

instance AsStreamArgErr Error' where
  _StreamArgErr = _ErrorS . _StreamArgErr
  
instance AsParseErr BuildWordErr where
  _ParseErr' = _BuildWordErrP . _ParseErr'

instance AsTypeClash OOPErr where
  _TypeClash = _OOPErrT . _TypeClash

instance AsTypeClash Error' where
  _TypeClash = _ErrorT . _TypeClash

instance AsParseErr Error' where
  _ParseErr' = _ErrorP . _ParseErr'

instance AsOOPErr Error' where
  _OOPErr = _ErrorO . _OOPErr

