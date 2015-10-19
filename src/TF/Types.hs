{-# LANGUAGE OverloadedStrings,  TypeFamilies, DeriveFunctor, GADTs, TemplateHaskell, FunctionalDependencies, FlexibleInstances,  NoMonomorphismRestriction, DeriveGeneric,DeriveDataTypeable, DataKinds #-}
module TF.Types where

import Prelude hiding (Word)
import  Control.Lens (Prism,prism, makeWrapped,makePrisms)


import Lens.Simple 
  
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
import TF.Type.Nodes
import TF.Type.StackEffect

  
import qualified Data.Tree.Zipper as TreeZ

--------------------------------------
------- STREAM ARGUMENT TYPES --------  
--------------------------------------
type SpacesDelimitedParsing = String

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

-- makePrisms ''DataType
-- makePrisms ''BasicType
-- makeFields ''DefiningArg
-- makeFields ''StreamArg
-- makePrisms ''RuntimeSpecification
-- makeFields ''ExecutionToken


type ReferenceDegree = Int

getIndex t = t ^. _2


data ChangeState =   ReferenceDegree Identifier Int 
                   | ResolveUnknown Identifier DataType 
                   deriving (Show,Eq)
makeTraversals ''ChangeState

                       



type Parsed = String
type Name = String
type Description = String

_NoReferenceIndexed :: Prism IndexedStackType IndexedStackType IndexedStackType IndexedStackType
_NoReferenceIndexed = prism id (\s -> case s of
                                  noref@(NoReference _, _) -> Right noref
                                  x -> Left x)

type SingleSemiEffect = [StackArg]
type SemiEffect = [SingleSemiEffect]


data Optional = Sem Semantics | NotSet | Undefined deriving (Show,Eq)

data CompilationSemantics  = CompSemDefined (Optional )
                              | APPEND_EXECUTION
                              | IMMEDIATE_EXECUTION
                                deriving (Show,Eq)

data InterpretationSemantics = IntSemDefined Optional 
                                 | ADOPT_EXECUTION
                                 deriving (Show, Eq)

newtype ExecutionSemantics = ExecSem (Optional ) deriving (Show, Eq)

newtype RuntimeSemantics = RunSem (Optional ) deriving (Show, Eq)

data ColonDefinitionProcessed = ColonDefinitionProcessed {
    _cdefprocColonDefinition :: ColonDefinition
  , _cdefprocProcessedEffects :: EffectsByPhase } deriving Show

data Definition = ColDef ColonDefinitionProcessed | CreateDef [StackEffect] deriving Show

type CompExecEffect = (StackEffect, StackEffect)
type StackEffectPair = (StackEffect, StackEffect)


newtype ForthEffect = ForthEffect ([StackEffectPair], Intersections) deriving (Show, Eq)
  

data FullStackEffect = FullStackEffect {
    _fullstackeffectEffects :: MultiStackEffect
  , _fullstackeffectIntersection :: Intersections
       } deriving (Show, Eq)

data CheckEffectsConfig = CheckEffectsConfig {
  _checkconfigForthWordOrExpr :: Maybe Node
, _checkconfigIsForcedAssertion :: Bool
, _checkconfigCheckState :: SemState
}  deriving (Show)

defCheckEffectsConfig = CheckEffectsConfig Nothing False INTERPRETSTATE


data Word = Word {
              _wordParsed :: Parsable
            , _wordName :: String
            , _wordRuntime :: RuntimeSemantics 
            , _wordExecution :: ExecutionSemantics
            , _wordCompilation :: CompilationSemantics
            , _wordInterpretation :: InterpretationSemantics
            , _wordIsImmediate :: Bool
            , _wordIntersections :: Intersections
              } deriving (Show, Eq)


newtype Intersection = Intersection Bool deriving (Show)

data StackEffectsWI = StackEffectsWI {
    stefwiMultiEffects :: [StackEffect]
  , stefwiIntersection :: Intersection } deriving (Show)
                          
-- data EffectsByPhase = Forced [StackEffect]
data EffectsByPhase = Forced StackEffectsWI
                    -- | Checked ([StackEffect],Bool)
                    | Checked StackEffectsWI -- ([StackEffect],Bool)
                    | NotChecked
                    | Failed String  deriving (Show)

data ColonDefinition = ColonDefinition {
                       _cdefBody        :: [Node]
                     , _cdefMeta :: ColonDefinitionMeta
                     } deriving (Show)

data ColonDefinitionMeta = ColonDefinitionMeta {
    _cdefinfoName :: String
  , _cdefinfoIsImmediate :: Bool
    } deriving (Show, Read, Eq)
makeFields ''ColonDefinitionMeta

newtype Trace = Trace {
  _traceParsedExpressions :: TreeZ.TreePos TreeZ.Full String
} deriving (Show,Eq)

data ParseState = ParseState {
                   _definedWords'        :: M.Map String Definition
                 , _coreWords           :: M.Map Parsable Word
                 , _stateVar            :: SemState
                 , _currentCompiling :: Bool
                 , _effects :: ForthEffect

                 , _classInterfaces :: M.Map ClassName [(Method, OOMethodSem)]
                 , _classFields :: M.Map ClassName [(Variable, OOFieldSem)]
                 , _subtypeRelation :: S.Set (BasicType, BasicType)
                 , _unresolvedArgsTypes :: M.Map Identifier StackEffect
                 , _inputStreamAssertions :: [StackEffect]
                 , _trace :: Trace
               } deriving (Show)
makeLenses ''ParseState

data BuildState = BS { _state :: SemanticsState
                     , _word :: Word
                     } deriving (Show,Eq)

data ParseEffectResult = ParseEffectResult {
                             _parsedParsedEffects :: [([IndexedStackType], [IndexedStackType])]
                           , _parsedStreamArguments :: [DefiningOrNot]
                           , _parsedForcedEffect :: Bool
                           , _parsedIsIntersection :: Bool
                           } deriving (Show,Eq)

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
                         | END deriving (Functor, Show)

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
} deriving (Show,Eq)

  
data CheckFailure = CheckFailure {
  _checkCurrentEffects :: [CompExecEffect],
  _checkNewEffects :: [CompExecEffect]
} deriving (Show,Eq)

data AssertFailure = AssertFailure {
  _assertfailCurrentEffects :: [CompExecEffect],
  _assertfailNewEffects :: [CompExecEffect]
} deriving (Show,Eq)
  
type Depth = Int
data Info = Info {
  _infoCheckedExpressions :: [(Node, Depth)]
  , _infoFailures :: [CheckFailure]
  , _infoAssertFailures :: [AssertFailure]

  } deriving (Show)

instance Monoid Info where
  mempty = Info [] [] []
  mappend (Info exprs1 fails1 asserts1) (Info exprs2 fails2 asserts2) = Info (exprs1 ++ exprs2) (fails1 ++ fails2) (asserts1 ++ asserts2)

data CustomState = CustomState {
  _customIdentifier :: Int
, _customDepth :: Int
, _customWordsMap :: M.Map Parsable Word
} deriving (Show,Eq)



makeFields ''Trace
makeWrapped ''Trace
makeFields ''Info
makeFields ''ParseStackEffectsConfig
makeFields ''CustomState
makeFields ''ColonDefinition
makeFields ''ParseConfig
makeFields ''CheckEffectsConfig
makeFields ''ColonDefinitionProcessed
makeWrapped ''ForthEffect
makeLenses ''BuildState
makeFields ''ParseEffectResult
makeFields ''ParseState
makePrisms ''EffectsByPhase
makeFields ''StackEffectsWI
makeFields ''Word
makeTraversals ''Optional
makeTraversals ''CompilationSemantics
makeTraversals ''Definition
makeTraversals ''InterpretationSemantics
makeWrapped ''ExecutionSemantics
makeWrapped ''RuntimeSemantics

_WordIdentifier = _Left
_Number = _Right


type UnknownWithState = (Unknown, SemState)

defaultSemantics = Semantics "" Nothing (MultiStackEffect [])

_Error = _Left
_Result = _Right

-- type DefOrWord = Either NameOfDefinition Word
type DefOrWord = Either NameOfDefinition String
_Def = _Left
_Word = _Right

type Token = Either Unknown Word
_Unknown = _Left


isImmediateColonDefinition = view $ meta.isImmediate 

                      
_TypeCheckPending = _Left
_TypeCheckDone    = _Right

_ColonDefinition = _ColDef
_CreateDefinition = _CreateDef


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
                                     } deriving (Show,Eq)
makeFields ''WildcardResult

unStackEffectM :: MaybeT (ExceptT String IO) a -> IO (Either String (Maybe a))
unStackEffectM = runExceptT . runMaybeT

data ParseStackState = ParseStackState { 
                               parsestateBefore :: [[[IndexedStackType]]]
                             , parsestateAfter :: [[[IndexedStackType]]]
                             -- , _definedWords :: [Definition]
                             , parsestateStreamArguments :: [[DefiningOrNot]]
                             , parsestateForced :: Bool
                             }  deriving (Show, Eq)
makeLens ''ParseStackState


data ParseStacksState = ParseStacksState {
                                types :: [PrimType]
                              , currentEffect :: ParseStackState
                              , previousEffects :: [ParseStackState]
                              , forced' :: Bool
                              , isIntersect :: Bool
                              } deriving (Show, Eq)
makeLens ''ParseStacksState

type ParseStackEffectsM = ParsecT String ParseStacksState (Reader ParseStackEffectsConfig)

instance HasDefault ParseStacksState where
  def = ParseStacksState forthTypes def [] False False 


instance HasDefault ParseStackState where
  def = ParseStackState [] [] [] False

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
  def = Word (Left "") def def def def def def (Intersections False False)

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
