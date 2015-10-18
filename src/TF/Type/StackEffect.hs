{-# LANGUAGE OverloadedStrings,  TypeFamilies, DeriveFunctor, GADTs, TemplateHaskell, FunctionalDependencies, FlexibleInstances,  NoMonomorphismRestriction, DeriveGeneric,DeriveDataTypeable, DataKinds #-}

module TF.Type.StackEffect where

import TF.ForthTypes
import TF.TH

type DefiningOrNot = Either DefiningArg StreamArg
type IndexedStackType = (DataType, Maybe Int)
type Identifier = Int
type ClassName = String

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
    _executiontokenSymbol :: TypeSymbol
  , _executiontokenRuntimeSpecified :: Maybe RuntimeSpecification }
                    deriving (Show,Ord,Eq)
data BasicType = ClassType ClassName 
               | PrimType PrimType 
               | ExecutionType ExecutionToken
               deriving (Show,Eq,Ord)
data DefiningArg = DefiningArg {
                      _definingName :: String
                    , _definingResolved :: Maybe String
                    , _definingArgType :: Maybe IndexedStackType
                    , _definingEndDelimiter :: Maybe String

                    , _definingRuntimeEffect :: Maybe [(StackEffect,StackEffect)]
                      -- the effect specification in comments:
                    , _definingRuntimeSpecified :: Maybe StackEffect 
                    }  deriving (Show,Eq,Ord)
data StreamArg = StreamArg {
                       _streamName :: String
                     , _streamResolved :: Maybe String
                     , _streamEndDelimiter :: Maybe String
                     , _streamRuntimeSpecified :: Maybe RuntimeSpecification
                    } deriving (Show,Eq,Ord)
data StackEffect = StackEffect {
                  _stackeffectBefore :: [IndexedStackType]
               ,  _stackeffectStreamArgs :: [DefiningOrNot]
               ,  _stackeffectAfter :: [IndexedStackType]
                 }  deriving (Show, Eq,Ord)
makeFields ''StackEffect

type DataStackEffect = [StackEffect]

data MultiStackEffect = MultiStackEffect {
  _steffsMultiEffects :: DataStackEffect
  } deriving (Show, Eq)
