{-# LANGUAGE LambdaCase,OverloadedStrings, StandaloneDeriving, TypeFamilies, DeriveFunctor, GADTs, TemplateHaskell, FunctionalDependencies, FlexibleInstances, GADTs, NoMonomorphismRestriction, DeriveGeneric,DeriveDataTypeable, DataKinds #-}
module TF.Types where

import Prelude hiding (Word)
import  Control.Lens hiding (makeFields)
import TF.TH

import           Data.Data hiding (DataType)
import           Control.Monad.Free
import           Control.Monad.State
import           Control.Monad.Writer
import           Control.Monad.Reader
import GHC.Generics (Generic)
import Lens.Family.Total hiding ((&))
import           Control.Monad.RWS
import Data.Tree
import           Control.Error as E

import           Text.Parsec hiding (runParser, char)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as Te


import TF.ForthTypes
import TF.Errors

type Identifier = Int
type ClassName = String


------------------------------------
------- > KIND OF FORTH TYPES ------
------------------------------------

data DataType = Dynamic
              | WildcardWrapper
              | Wildcard
              | UnknownType Identifier
              | Reference DataType
              | NoReference BasicType
              deriving (Show,Read,Eq,Data,Typeable, Ord)

data BasicType = ClassType ClassName 
               | PrimType PrimType 
               | ExecutionType ExecutionToken
               deriving (Show,Ord,Read,Eq,Data,Typeable)

type IndexedStackType = (DataType, Maybe Int)
                        
type UniqueArg = Int
data RuntimeSpecification = NoR |
                            UnknownR UniqueArg |
                            KnownR StackEffect |
                            ResolvedR UniqueArg StackEffect deriving (Show,Read,Eq,Data,Typeable, Ord)
data ExecutionToken = ExecutionToken { _executiontokenSymbol :: TypeSymbol
                                     , _executiontokenRuntimeSpecified :: Maybe RuntimeSpecification
                                     } deriving (Show,Ord,Read,Eq,Data,Typeable)


refDegree :: DataType -> Int
refDegree (Reference x) = 1 + refDegree x
refDegree (NoReference x) = 0
refDegree (Wildcard) = 0
refDegree (Dynamic) = 0
refDegree (WildcardWrapper) = 0
refDegree (UnknownType _) = 0

baseType :: IndexedStackType -> IndexedStackType
baseType (arg, i) = (baseType' arg, i)

setBaseType :: DataType -> DataType -> DataType
setBaseType new (NoReference _) = new
setBaseType new (Reference old) = Reference $ setBaseType new old
setBaseType new old = new 

baseType' :: DataType -> DataType
baseType' Dynamic = Dynamic
baseType' Wildcard = Wildcard
baseType' WildcardWrapper = WildcardWrapper
baseType' (NoReference r) = NoReference r
baseType' (Reference d) = baseType' d
baseType' (UnknownType i) = UnknownType i

removeDegree 0 x = x
removeDegree x (Reference y) = removeDegree (x-1) y
removeDegree x y = y

--------------------------------------
------- STREAM ARGUMENT TYPES --------  
--------------------------------------
type SpacesDelimitedParsing = String
-- data StringDelimitedParsing = StringDelimited { argName :: String
--                                               , delimiter :: String
--                                               } deriving (Show,Read,Eq,Data,Typeable)

data DefiningArg = DefiningArg {
                      _definingName :: String
                    , _definingResolved :: Maybe String
                    , _definingArgType :: Maybe IndexedStackType
                    , _definingEndDelimiter :: Maybe String

                    -- , _defargRuntimeEffect :: Maybe (Either [(StackEffect,StackEffect)] [(StackEffect,StackEffect)])
                    , _definingRuntimeEffect :: Maybe [(StackEffect,StackEffect)]
                      -- the effect specification in comments:
                    , _definingRuntimeSpecified :: Maybe StackEffect 
                    -- , _defargRuntimeChecked :: Bool
                    }  deriving (Show,Read,Eq,Data,Typeable, Ord)


type DefiningOrNot = Either DefiningArg StreamArg

data StreamArg = StreamArg {
                       _streamName :: String
                     , _streamResolved :: Maybe String
                     , _streamEndDelimiter :: Maybe String
                     , _streamRuntimeSpecified :: Maybe RuntimeSpecification
                    } deriving (Show,Read,Eq,Data,Typeable, Ord)

------ StackEffect -----
data StackEffect = StackEffect {
                  _stackeffectBefore :: [IndexedStackType]
               ,  _stackeffectStreamArgs :: [DefiningOrNot]
               ,  _stackeffectAfter :: [IndexedStackType]
                 }  deriving (Show, Ord, Read, Eq, Data, Typeable, Generic)
makeFields ''StackEffect


type DataArgOrStreamArg a b = Either a b
_DataType = _Left
_StreamArg = _Right

type StackArg = DataArgOrStreamArg [IndexedStackType] DefiningOrNot
type StackArg' = DataArgOrStreamArg IndexedStackType DefiningOrNot
type StackArg'' = DataArgOrStreamArg IndexedStackType DefiningOrNot

-- type DefiningOrNot' a = Either a a
_Defining = _Left
_NotDefining = _Right

_RuntimeProcessed = _Left
_RuntimeNotProcessed = _Right
_UnknownRuntimeSpecification = _Left
_KnownRuntimeSpecification = _Right

makePrisms ''DataType
makePrisms ''BasicType
makeFields ''DefiningArg
makeFields ''StreamArg
makePrisms ''RuntimeSpecification
makeFields ''ExecutionToken

-- printSubtypes = putStrLn . drawForest $ fmap (fmap (render . P.realtype)) (subtypeForest forthTypes getSubtypes)

-------------------------------
------- > FORTH TYPES ---------  
-------------------------------
subtypeForest :: [BasicType] -> (BasicType -> [BasicType]) -> Forest BasicType
subtypeForest forthTypes' getSubTypes' = unfoldForest getSubTypesOf forthTypes'
   where
     getSubTypesOf :: BasicType -> (BasicType, [BasicType])
     getSubTypesOf supertype = (supertype, getSubTypes' supertype)

getSubtypes :: PrimType -> [PrimType]
getSubtypes (PT U _ _ _) = [plusN, addr]
getSubtypes (PT ADDR _ _ _)  = [caddr]
getSubtypes (PT CADDR _ _ _)  = [aaddr]
getSubtypes (PT Plus_N _ _ _)  = [char]
getSubtypes (PT N _ _ _)  = [plusN]
getSubtypes _ = []

subtypeRelation' :: [BasicType] -> (PrimType -> [PrimType]) -> S.Set (BasicType, BasicType)
subtypeRelation' forthTypes' getSubTypes' = S.fromList [(t1, t2) | t1 <- forthTypes',
                                            t2 <- forthTypes',
                                            let forest = subtypeForest forthTypes' (dimap (^?! _PrimType) (map PrimType) getSubTypes'),
                                            isSubtypeOf t1 t2 forest]

defaultSubtypeRelation :: S.Set (BasicType, BasicType)
defaultSubtypeRelation = subtypeRelation' primitiveTypes  getSubtypes

primitiveTypes = map PrimType forthTypes

isSubtypeOf :: BasicType -> BasicType -> Forest BasicType -> Bool

isSubtypeOf t1 t2 forest | t1 == t2  = True
isSubtypeOf t1 t2 forest = any isSubTypeOf' $ forest
  where
    isSubTypeOf' tree 
        | rootLabel tree == t2   = not . null $ concatMap (filter (== t1) . depth') (subForest tree)
        | rootLabel tree /= t2   = False
-------------------------------
------- < FORTH TYPES ---------  
-------------------------------

depth' :: Tree a -> [a]
depth' (Node x []) = [x]
depth' (Node x ts) = x : concatMap depth' ts


type ReferenceDegree = Int

getIndex t = t ^. _2


data ChangeState =   ReferenceDegree Identifier Int 
                   | ResolveUnknown Identifier DataType 
                   deriving (Show,Read,Eq,Data,Typeable)
makePrisms ''ChangeState

                       



type Parsed = String
type Name = String
type Description = String

_NoReferenceIndexed :: Prism IndexedStackType IndexedStackType IndexedStackType IndexedStackType
_NoReferenceIndexed = prism id (\s -> case s of
                                  noref@(NoReference _, _) -> Right noref
                                  x -> Left x)

type CompiledOrExecuted a = Either a a 
_Executed = _Right
_Compiled = _Left

data Threes a b c = One'  a | Two' b |  Three' c  deriving (Show, Read, Eq, Data, Typeable, Generic)
makePrisms ''Threes

type CompiledExecutedOrBoth a = Threes a a (a,a)
instance (Empty a, Empty b, Empty c) => Empty (Threes a b c)
                                      
chosen'' f (One' y) = One' `fmap` f y
chosen'' f (Two' y) = Two' `fmap` f y
_CompiledEff = _One'
_ExecutedEff = _Two'
_CompAndExecutedEff = _Three'

newtype UnresolvedArgsTypesState = UnresolvedArgsTypesState {
  _uatsIndexToIdentifier :: M.Map Int UniqueArg
}  deriving (Show, Read, Eq, Data, Typeable, Generic)
makeFields ''UnresolvedArgsTypesState


type DataStackEffect = [StackEffect]
type SingleSemiEffect = [StackArg]
type SemiEffect = [SingleSemiEffect]

data SemState = INTERPRETSTATE | COMPILESTATE deriving (Show, Read, Eq, Data, Typeable)

data MultiStackEffect = MultiStackEffect {
  _steffsMultiEffects :: DataStackEffect
  } deriving (Show, Read, Eq, Data, Typeable)
makeWrapped ''MultiStackEffect


data Optional = Sem Semantics | NotSet | Undefined deriving (Show, Read ,Eq, Data, Typeable)

data CompilationSemantics  = CompSemDefined (Optional )
                              | APPEND_EXECUTION
                              | IMMEDIATE_EXECUTION
                                deriving (Show, Read ,Eq, Data, Typeable)

data InterpretationSemantics = IntSemDefined Optional 
                                 | ADOPT_EXECUTION
                                 deriving (Show, Read ,Eq, Data, Typeable)

newtype ExecutionSemantics = ExecSem (Optional ) deriving (Show, Read, Eq, Data, Typeable)

newtype RuntimeSemantics = RunSem (Optional ) deriving (Show, Read, Eq, Data, Typeable)

data Semantics = Semantics {
                     _semDescription :: String
                   , _semEnter :: Maybe SemState
                   , _semEffectsOfStack:: MultiStackEffect
                      } deriving (Show, Read, Eq, Data, Typeable)

type NameOfDefinition = String  
type Node = Either ForthWord Expr
type Variable = String
type Method = String
type OOFieldSem = OOFieldSem' StackEffect

type Number = ()
type Parsable = Either Te.Text Number -- Str String | Number deriving (Show, Read, Eq, Data, Typeable)

type ColonDefinition' = (ColonDefinition, EffectsByPhase)
type Definition' = Either ColonDefinition' [StackEffect]

type CompExecEffect = (StackEffect, StackEffect)
type StackEffectPair = (StackEffect, StackEffect)
type ForthWordOrExpr = Either ForthWord Expr
_ForthWord = _Left
_Expr = _Right

newtype ForthEffect = ForthEffect ([StackEffectPair], IntersectionType) deriving (Show, Read, Eq, Data, Typeable)
  
data IntersectionType = IntersectionType {
    _intersectCompileEffect :: Bool
  , _intersectExecEffect :: Bool
  } deriving (Show,Read,Eq,Data,Typeable)

data CheckEffectsConfig = CheckEffectsConfig {
  _checkconfigForthWordOrExpr :: Maybe ForthWordOrExpr
, _checkconfigIsForcedAssertion :: Bool
, _checkconfigCheckState :: SemState
}  deriving (Show,Read,Eq,Data,Typeable)

defCheckEffectsConfig = CheckEffectsConfig Nothing False INTERPRETSTATE

data ControlStructure = IfExpr [Node]
                      | IfElseExpr [Node] [Node]
                      | DoLoop [Node]
                      | DoPlusLoop [Node]
                      | BeginUntil [Node]
                      | BeginWhileRepeat [Node] [Node]
          deriving (Show, Read, Data, Typeable, Eq)

data OOPExpr = Class ClassName [(Variable, OOFieldSem)] [(Method, OOMethodSem)] ClassName
          | SuperClassMethodCall ClassName Method
          | MethodCall (CompiledOrExecuted Method)
          | NewObject (CompiledOrExecuted ClassName)
          | FieldCall (CompiledOrExecuted Variable)
          | NoName (Maybe ([StackEffect], Bool)) [Node] ClassName Method
          | NoNameClash (Maybe ([StackEffect], Bool)) ClassName Method
          deriving (Show, Read, Data, Typeable, Eq)

data Expr =  ColonExpr String (Maybe (Semantics, Bool)) [Node]
          | ColonExprImmediate String (Maybe (Semantics, Bool)) [Node]
          | ColonExprClash String (Maybe (Semantics, Bool))
          | Postpone (Either NameOfDefinition Word)
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
          deriving (Show, Read, Data, Typeable, Eq)

data Word = Word {
              _wordParsed :: Parsable
            , _wordName :: String
            , _wordRuntime :: RuntimeSemantics 
            , _wordExecution :: ExecutionSemantics
            , _wordCompilation :: CompilationSemantics
            , _wordInterpretation :: InterpretationSemantics
            , _wordIsImmediate :: Bool
            , _wordIntersectionType :: IntersectionType
              } deriving (Show, Read, Eq, Data, Typeable)

newtype Unknown = Unknown {
                     _unknownName :: String
                  } deriving (Show, Read, Eq, Data, Typeable)

data ParsedWord = ParsedWord {
                   _pwordParsed :: Parsable
                 , _pwordName :: String
                 , _pwordStacksEffects :: CompiledExecutedOrBoth MultiStackEffect
                 , _pwordEnter :: Maybe SemState
                 , _pwordIntersectionType :: IntersectionType
                  } deriving (Show, Read, Eq, Data, Typeable)

data ForthWord = UnknownE Unknown
               | DefE (CompiledOrExecuted (NameOfDefinition, [StackEffect]))
               | KnownWord ParsedWord
               deriving (Eq, Show, Data, Typeable, Read)

data OOFieldSem' a = ByFieldDefinition a
                   | InferredByField a
                   deriving (Show, Read, Data, Typeable, Eq, Functor)

data OOMethodSem = Empty
                 | ByDefinition ([StackEffect], Bool)
                 | InferredByMethod ([StackEffect], Bool)
                 deriving (Show, Read, Data, Typeable, Eq)
data EffectsByPhase = Forced [StackEffect]
                    | Checked ([StackEffect],Bool)
                    | NotChecked
                    | Failed String  deriving (Show, Read, Data, Typeable, Eq)

data ColonDefinition = ColonDefinition {
                       _cdefName        :: String
                     , _cdefBody        :: [ForthWordOrExpr]
                     , _cdefIsImmediate :: Bool
                     } deriving (Show, Read, Eq, Data, Typeable)

data ParseState = ParseState {
                   _definedWords'        :: M.Map String Definition'
                 , _coreWords           :: M.Map Parsable Word
                 , _stateVar            :: SemState
                 , _currentCompiling :: Bool
                 , _effects :: ForthEffect

                 , _classInterfaces :: M.Map ClassName [(Method, OOMethodSem)]
                 , _classFields :: M.Map ClassName [(Variable, OOFieldSem)]
                 , _subtypeRelation :: S.Set (BasicType, BasicType)
                 , _unresolvedArgsTypes :: M.Map Identifier StackEffect
                 , _inputStreamAssertions :: [StackEffect]

               } deriving (Show, Read, Data, Typeable, Eq)
makeLenses ''ParseState

data BuildState = BS { _state :: SemanticsState
                     , _word :: Word
                     } deriving (Show,Read,Eq,Data,Typeable)

data ParseEffectResult = ParseEffectResult {
                             _parsedParsedEffects :: [([IndexedStackType], [IndexedStackType])]
                           , _parsedStreamArguments :: [DefiningOrNot]
                           , _parsedForcedEffect :: Bool
                           , _parsedIsIntersection :: Bool
                           } deriving (Show,Read,Eq,Data,Typeable)

data WordDefinition cont = COMPILE_COMING cont
                         | IMMEDIATE cont
                         | PARSED_NUM cont
                         | PARSED_STR Te.Text cont
                         | NAME String cont
                         | ENTER SemState cont
                         | EFFECT String cont
                         | EFFECT_UNDEFINED cont
                         | DESCRIPTION String cont
                         | COMPILATION_START cont
                         | COMPILATION_END cont
                         | REDEFINING_LATEST_CREATED String cont
                         | INTERPRETATION_START cont
                         | INTERPRETATION_END cont
                         | RUNTIME_START cont
                         | RUNTIME_END cont
                         | END deriving (Functor, Show, Read, Data, Typeable)

data ParseConfig = ParseConfig {
    _configTypeCheck :: Bool
  , _configTopLevelEmpty :: Bool
  , _configReadFromStream :: Bool
  , _configAllowMultipleEffects :: Bool
  , _configAllowLocalFailure :: Bool
  , _configAllCoreDynamic :: Bool
  , _configAllowDynamicInStackComments :: Bool
  , _configAllowCasts :: Bool
  , _configThirdParty :: [Free WordDefinition ()]
  , _configAllowForcedEffects :: Bool
  , _configSubtypes :: PrimType -> [PrimType]
  , _configAllowOOP :: Bool
  }  deriving (Typeable)

data SemanticsState = COMPILATION | EXECUTION | INTERPRETATION | RUNTIME deriving (Show,Read,Eq,Data,Typeable)

data ParseStackEffectsConfig = ParseStackEffectsConfig {
 _stackeffClassNames :: [ClassName]
 , _stackeffOnlyAfter :: Bool
 , _stackeffAllowDynamicInStackComments :: Bool
} deriving (Show,Read,Eq,Data,Typeable)

  
data CheckFailure = CheckFailure {
  _checkCurrentEffects :: [CompExecEffect],
  _checkNewEffects :: [CompExecEffect]
} deriving (Show,Read,Eq,Data,Typeable)

data AssertFailure = AssertFailure {
  _assertfailCurrentEffects :: [CompExecEffect],
  _assertfailNewEffects :: [CompExecEffect]
} deriving (Show,Read,Eq,Data,Typeable)
  
type Depth = Int
data Info = Info {
  _infoCheckedExpressions :: [(ForthWordOrExpr, Depth)]
  , _infoFailures :: [CheckFailure]
  , _infoAssertFailures :: [AssertFailure]

  } deriving (Show,Read,Eq,Data,Typeable)

instance Monoid Info where
  mempty = Info [] [] []
  mappend (Info exprs1 fails1 asserts1) (Info exprs2 fails2 asserts2) = Info (exprs1 ++ exprs2) (fails1 ++ fails2) (asserts1 ++ asserts2)

data CustomState = CustomState {
  _customIdentifier :: Int
, _customDepth :: Int
, _customWordsMap :: M.Map Parsable Word
} deriving (Show,Read,Eq,Data,Typeable)



makeFields ''Info
makeFields ''ParseStackEffectsConfig
makeFields ''CustomState
makeFields ''ColonDefinition
makeFields ''ParseConfig
makeFields ''CheckEffectsConfig
makeFields ''IntersectionType
makeWrapped ''ForthEffect
makeLenses ''BuildState
makeFields ''ParseEffectResult
makeFields ''ParseState
makePrisms ''EffectsByPhase
makePrisms ''OOMethodSem
makePrisms ''OOFieldSem'
makePrisms ''ForthWord
makeFields ''ParsedWord
makeWrapped ''Unknown
makeFields ''Unknown
makeFields ''Word
makePrisms ''Expr
makeFields ''Semantics
makePrisms ''Optional
makePrisms ''CompilationSemantics
makePrisms ''InterpretationSemantics
makeWrapped ''ExecutionSemantics
makeWrapped ''RuntimeSemantics

_WordIdentifier = _Left
_Number = _Right


type UnknownWithState = (Unknown, SemState)

defaultSemantics = Semantics "" Nothing (MultiStackEffect [])

_Error = _Left
_Result = _Right

type DefOrWord = Either NameOfDefinition Word
_Def = _Left
_Word = _Right

type Token = Either Unknown Word
_Unknown = _Left


isImmediateColonDefinition = view isImmediate 

                      
_TypeCheckPending = _Left
_TypeCheckDone    = _Right

_ColonDefinition = _Left
_CreateDefinition = _Right


emptyEffect = [StackEffect [] [] []]




    
  
        
type Script'  = RWST ParseConfig () CustomState (ExceptT Error' (Writer Info)) 
type StackEffectM = Script'  
type StackEffects = (StackEffect, StackEffect)
type CheckerM = ParsecT [Token] ParseState StackEffectM 
type CheckNodesT = ([Node] -> CheckerM ForthEffect)
type CheckEffectsT = ForthEffect -> ReaderT CheckEffectsConfig CheckerM ()
type CollectEffectsT = Node -> CheckerM ()
type CheckerM' = ReaderT (CheckNodesT, CheckEffectsT, CollectEffectsT) CheckerM
type StackRuleM = ExceptT SemState (ReaderT CheckEffectsConfig CheckerM)

type ParseWord = Te.Text -> CheckerM ParsedWord
type IsKnownWord =  CheckerM (Maybe (Either ForthWord DefOrWord) )
type ParseStackEffectSemantics = (String -> ParseStackEffectsConfig -> Script' ParseEffectResult) -> CheckerM (Semantics, Bool)
type ParseNode = CheckerM Node
type ParseNodeWithout = [Word] -> CheckerM Node

data ExpressionsEnv = ExpressionEnv {
    _exprenvParseWord' :: ParseWord
  , _exprenvIsKnownWord' :: IsKnownWord
  , _exprenvParseStackEffectSemantics' :: ParseStackEffectSemantics
  , _exprenvParseNode' :: ParseNode
  , _exprenvParseNodeWithout' :: ParseNodeWithout
  } deriving (Typeable)

makeFields ''ExpressionsEnv

type ExpressionsM = ReaderT ExpressionsEnv CheckerM

liftUp = lift . lift

data WildcardResult = WildcardResult { wildcardEffs :: (StackEffects, StackEffects) 
                                     , wildcardLog1 :: [ChangeState]
                                     , wildcardLog2 :: [ChangeState]
                                     } deriving (Show,Read,Eq,Data,Typeable)
makeFields ''WildcardResult

unStackEffectM :: MaybeT (ExceptT String IO) a -> IO (Either String (Maybe a))
unStackEffectM = runExceptT . runMaybeT


class HasDefault d where
  def :: d

instance HasDefault [x] where
  def = []

instance HasDefault (CompilationSemantics ) where
  def = CompSemDefined NotSet

instance HasDefault (InterpretationSemantics ) where
  def = IntSemDefined NotSet

instance HasDefault Optional where
  def = NotSet

instance HasDefault ExecutionSemantics  where
  def = ExecSem $ Sem def

instance HasDefault (RuntimeSemantics ) where
  def = RunSem def

instance HasDefault Word where
  def = Word (Left "") def def def def def def (IntersectionType False False)

instance HasDefault Semantics where
  def = Semantics def def def

instance HasDefault MultiStackEffect where
  def = MultiStackEffect []

instance HasDefault Bool where
  def = False

instance HasDefault BuildState where
  def = BS def def 

instance HasDefault SemanticsState where
  def = EXECUTION

instance HasDefault (Maybe x) where
  def = Nothing
