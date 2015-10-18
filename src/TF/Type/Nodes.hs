{-# LANGUAGE OverloadedStrings,  TypeFamilies, DeriveFunctor, GADTs, TemplateHaskell, FunctionalDependencies, FlexibleInstances,  NoMonomorphismRestriction, DeriveGeneric,DeriveDataTypeable, DataKinds #-}

module TF.Type.Nodes where

import qualified Data.Text as Te
import TF.TH
import TF.ForthTypes
import  Control.Lens hiding (makeFields)
import TF.Type.StackEffect
import Lens.Family.Total (Empty)
import GHC.Generics (Generic)
import           Data.Data hiding (DataType)
-- import TF.Type.Expressions.Expr (Expr(..))
-- import TF.Type.Expressions.OOP (OOPExpr(..))

type Number = ()
type Parsable = Either Te.Text Number -- Str String | Number deriving (Show, Eq)
type NameOfDefinition = String  
type CompiledOrExecuted a = Either a a 
_Executed = _Right
_Compiled = _Left

newtype Unknown = Unknown {
                     _unknownName :: String
                  } deriving (Show, Eq)
data Threes a b c = One'  a | Two' b |  Three' c  deriving (Show, Eq, Generic)
makePrisms ''Threes

type CompiledExecutedOrBoth a = Threes a a (a,a)
instance (Empty a, Empty b, Empty c) => Empty (Threes a b c)
                                      
chosen'' f (One' y) = One' `fmap` f y
chosen'' f (Two' y) = Two' `fmap` f y
_CompiledEff = _One'
_ExecutedEff = _Two'
_CompAndExecutedEff = _Three'


                      
data SemState = INTERPRETSTATE | COMPILESTATE deriving (Show, Eq)
data Semantics = Semantics {
                     _semDescription :: String
                   , _semEnter :: Maybe SemState
                   , _semEffectsOfStack:: MultiStackEffect
                      } deriving (Show, Eq)
             
data Intersections = Intersections {
    _intersectCompileEffect :: Bool
  , _intersectExecEffect :: Bool
  } deriving (Show,Eq)
data ParsedWord = ParsedWord {
                   _pwordParsed :: Parsable
                 , _pwordName :: String
                 , _pwordStacksEffects :: CompiledExecutedOrBoth MultiStackEffect
                 , _pwordEnter :: Maybe SemState
                 , _pwordIntersections :: Intersections
                  } deriving (Show, Eq)
data ForthWord = UnknownE Unknown
               | DefE (CompiledOrExecuted (NameOfDefinition, [StackEffect]))
               | KnownWord ParsedWord
               deriving (Eq, Show)





data Node = ForthWord ForthWord | Expr Expr deriving Show




data ControlStructure = IfExpr [Node]
                      | IfElseExpr [Node] [Node]
                      | DoLoop [Node]
                      | DoPlusLoop [Node]
                      | BeginUntil [Node]
                      | BeginWhileRepeat [Node] [Node]
          deriving (Show)


type NameOfWord = String
                   
data Expr =  ColonExpr String (Maybe (Semantics, Bool)) [Node]
          | ColonExprImmediate String (Maybe (Semantics, Bool)) [Node]
          | ColonExprClash String (Maybe (Semantics, Bool))
          | Postpone (Either NameOfDefinition NameOfWord)
          | PostponeImmediate ForthWord
          | Comment  [String]
          | Interpreted [Node]
          | Tick [StackEffect] ParsedWord
          | Create Node (Maybe ([Node], Node)) (Maybe [Node])
          | Execute (CompiledOrExecuted [StackEffect])
          | Assert (CompiledOrExecuted [StackEffect]) Bool
          | Cast (CompiledOrExecuted [StackEffect])
          | Include String
          | Require String
          | ControlExpr ControlStructure
          | OOPExpr OOPExpr
          deriving (Show)

type Variable = String
type Method = String
type OOFieldSem = OOFieldSem' StackEffect
data OOFieldSem' a = ByFieldDefinition a
                   | InferredByField a
                   deriving (Show, Eq, Functor)

data OOMethodSem = Empty
                 | ByDefinition ([StackEffect], Bool)
                 | InferredByMethod ([StackEffect], Bool)
                 deriving (Show, Eq)

data OOPExpr = Class ClassName [(Variable, OOFieldSem)] [(Method, OOMethodSem)] ClassName
          | SuperClassMethodCall ClassName Method
          | MethodCall (CompiledOrExecuted Method)
          | NewObject (CompiledOrExecuted ClassName)
          | FieldCall (CompiledOrExecuted Variable)
          | NoName (Maybe ([StackEffect], Bool)) [Node] ClassName Method
          | NoNameClash (Maybe ([StackEffect], Bool)) ClassName Method
          deriving (Show)
                                                     


-- makeFields ''StackEffect
makeWrapped ''MultiStackEffect
makeFields ''ParsedWord
makeWrapped ''Unknown
makeFields ''Unknown

makeFields ''Semantics
makePrisms ''ForthWord
makePrisms ''Expr
makePrisms ''Node

makePrisms ''OOMethodSem
makePrisms ''OOFieldSem'

makeFields ''Intersections