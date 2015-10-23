{-# LANGUAGE OverloadedStrings,  TypeFamilies, DeriveFunctor, GADTs, TemplateHaskell, FunctionalDependencies, FlexibleInstances,  NoMonomorphismRestriction, DeriveGeneric,DeriveDataTypeable, DataKinds #-}

module TF.Type.StackEffect where

import TF.ForthTypes
import TF.TH
import Lens.Simple 
import Control.Lens (makeWrapped)

-- type DefiningOrNot = Either DefiningArg StreamArg
data DefiningOrNot = Defining DefiningArg | NotDefining StreamArg deriving (Show,Eq,Ord)

-- type IndexedStackType = (DataType, Maybe Int)
data IndexedStackType = IndexedStackType {
    stackType :: DataType
  , typeIndex :: (Maybe Int) } deriving (Show,Eq,Ord)
type Identifier = Int
type ClassName = String


data DataArgOrStreamArg dataArg = DataArg dataArg | NonDataArg DefiningOrNot deriving (Show, Eq)

type StackArg = DataArgOrStreamArg [IndexedStackType]
type StackArg' = DataArgOrStreamArg IndexedStackType 
type StackArg'' = DataArgOrStreamArg IndexedStackType 
type SingleSemiEffect = [StackArg]
type SemiEffect = [SingleSemiEffect]


-- type DefiningOrNot' a = Either a a
-- _Defining = _Left
-- _NotDefining = _Right

data DataType = Dynamic
              | WildcardWrapper
              | Wildcard
              | UnknownType Identifier
              | Reference DataType
              | NoReference BasicType
              deriving (Show,Eq,Ord)

type UniqueArg = Int
data RuntimeSpecification = NoR |
                            UnknownR UniqueArg |
                            KnownR StackEffect |
                            ResolvedR UniqueArg StackEffect deriving (Show,Eq,Ord)

data ExecutionToken = ExecutionToken {
    symbol :: TypeSymbol
  , exectokenRuntimeSpecified :: Maybe RuntimeSpecification
  } deriving (Show,Ord,Eq)

data BasicType = ClassType ClassName 
               | PrimType PrimType 
               | ExecutionType ExecutionToken
               deriving (Show,Eq,Ord)

data ArgInfo a = ArgInfo {
                      argName :: String
                    , resolved :: Maybe String
                    , endDelimiter :: Maybe String
                    , runtimeSpecified :: Maybe a } deriving (Show,Eq,Ord)
  

                        
data DefiningArg = DefiningArg {
                      definingArgInfo :: ArgInfo StackEffect
                    , argType :: Maybe IndexedStackType
                    , runtimeEffect :: Maybe [(StackEffect,StackEffect)]
                    }  deriving (Show,Eq,Ord)

data StreamArg = StreamArg {
                      streamArgInfo :: ArgInfo RuntimeSpecification
                        
                    } deriving (Show,Eq,Ord)
data StackEffect = StackEffect {
                  before :: [IndexedStackType]
               ,  streamArgs :: [DefiningOrNot]
               ,  after :: [IndexedStackType]
                 }  deriving (Show, Eq,Ord)
makeLens ''StackEffect

type DataStackEffect = [StackEffect]

data MultiStackEffect = MultiStackEffect {
  _steffsMultiEffects :: DataStackEffect
  } deriving (Show, Eq)

makeTraversals ''DataType
makeTraversals ''BasicType
makeLens ''ArgInfo
makeLens ''DefiningArg
makeLens ''StreamArg
makeTraversals ''RuntimeSpecification
makeTraversals ''DefiningOrNot
makeLens ''ExecutionToken
makeLens ''IndexedStackType
