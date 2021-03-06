{-# LANGUAGE LambdaCase, TypeFamilies,  NoMonomorphismRestriction  #-}

module TF.Util where

import Prelude hiding (last)

import Control.Monad.Identity
import Control.Monad.State
import Lens.Family.Total hiding ((&))
import Control.Monad.Writer
import Control.Lens hiding (children)
import  Text.PrettyPrint (render)
import           Control.Error as E
import TF.Types hiding (isSubtypeOf)
import TF.HandleDegrees
import           Text.Parsec hiding (anyToken)
import qualified Data.Text as Te
import Debug.Trace
import qualified Data.Map as M
import Data.Maybe

import TF.Type.StackEffect
import TF.Type.Nodes


_forcedOrChecked :: Traversal' EffectsByPhase ( StackEffectsWI)
_forcedOrChecked f (Forced x) = Forced <$> f x
_forcedOrChecked f (Checked x) = Checked <$> f x
_forcedOrChecked f (Failed x) = pure $ Failed x
_forcedOrChecked f NotChecked = pure $ NotChecked

nodeIso = iso (\case { ForthWord x -> Left x ; Expr x -> Right x }) (\case { Left x -> ForthWord x; Right x -> Expr x }) 
argIso = iso (\case { DataArg x -> Left x ; NonDataArg x -> Right x }) (\case { Left x -> DataArg x; Right x -> NonDataArg x }) 
tokenIso = iso (\case { UnknownToken x -> Left x ; WordToken x -> Right x }) (\case { Left x -> UnknownToken x; Right x -> WordToken x }) 
defOrWordIso =  iso (\case { DefinitionName x -> Left x ; WordName x -> Right x }) (\case { Left x -> DefinitionName x; Right x -> WordName x }) 
compOrExecIso =  iso (\case { Compiled x -> Left x ; Executed x -> Right x }) (\case { Left x -> Compiled x; Right x -> Executed x }) 

iop = traceM
iopS = traceShowM


l3 = lift . lift . lift
l4 = lift . l3

logParser = False
iopP x = when logParser $ iop $ x

logChecker = False
iopC x = when logChecker $ iop $ x

logHasEffects = False
iopE x = when logHasEffects $ iop $ x

logEvaluator = False
iopEV x = when logEvaluator $ iop $ x

logStackCalculus = False
iopSC x = when logStackCalculus $ iop $ x

logSubtype = False
iopSu x = when logSubtype $ iop $ x

logWildcardRules = False
iopW x = when logWildcardRules $ iop $ x

chosen' = fmap (^?! _Left) . runExceptT
for = flip map

blockedWith caption f x = do
  f $ "-----" ++ caption
  blocked f x

blocked f x = do
  f "-----------------------"
  x
  f "-----------------------"


emptySt :: StackEffect
emptySt = StackEffect [] [] []

emptyIntersect = Intersections False False
emptyForthEffect = ForthEffect ([(emptySt, emptySt)], emptyIntersect)

withoutIntersect effs = ForthEffect (effs, emptyIntersect)
withoutIntersect' effs = (effs, emptyIntersect)

withIntersect i effs = ForthEffect (effs, i)

-- asTuples = (_case & (on _Compiled (\x -> view _Wrapped x `zip` repeat emptySt))
--                          & (on _Executed (\x -> zip (repeat emptySt) (view _Wrapped x))))
asTuples effs = case effs of
  Compiled effs -> view _Wrapped effs `zip` repeat emptySt
  Executed effs -> repeat emptySt `zip` view _Wrapped effs

effsAsTuples effs = case effs of
  Compiled effs -> effs `zip` repeat emptySt
  Executed effs -> repeat emptySt `zip` effs

fromThree' :: CompiledExecutedOrBoth MultiStackEffect -> [StackEffectPair]
fromThree' (One' x) = view _Wrapped x `zip` repeat emptySt
fromThree' (Two' x) = zip (repeat emptySt) (view _Wrapped x)
fromThree' (Three' (x,y)) = (x,y) & both %~ view _Wrapped & uncurry zip

-- compExecIso :: Simple Iso  (CompiledExecutedOrBoth StackEffect) CompExecEffect
-- compExecIso = iso fromThree toThree

fromThree :: CompiledExecutedOrBoth StackEffect -> StackEffectPair
fromThree (One' z) = (z, emptySt)
fromThree (Two' z) = (emptySt, z)
fromThree (Three' (z,y)) = (z,y)
          
toThree :: CompExecEffect -> CompiledExecutedOrBoth StackEffect
toThree (stE1, stE2)
  | stE1 == emptySt = Two' stE2
  | stE2 == emptySt = One' stE1
  | otherwise       = Three' (stE1, stE2)




new = review
labeled = flip label



resolveRuntimeType :: [(UniqueArg, StackEffect)] -> IndexedStackType -> IndexedStackType
resolveRuntimeType resolvedRuntimes (IndexedStackType t i') = IndexedStackType (setBaseType newType t) i'
  where
    newType = case baseType t of
      NoReference t' -> NoReference $ (case t' of
        exec@(ExecutionType execToken) -> ExecutionType $ execToken & _exectokenRuntimeSpecified._Just %~ (\case
          UnknownR i -> (case (lookup i resolvedRuntimes) of
              Just eff -> ResolvedR i eff
              Nothing  -> UnknownR i)
          x         -> x)
        z -> z)
      y               -> y
  
updatePos pos _ (_:_) = setSourceLine (setSourceColumn pos 1) 1
updatePos pos _ [] = pos
satisfy' f = tokenPrim show updatePos (\c -> if f c then Just c else Nothing)
noneOf' cs = satisfy' (`notElem` cs)

anyToken = satisfy' (const True)


getNextParameter :: CheckerM String
getNextParameter = do
  w <- anyToken :: CheckerM Token
  return . possWordAsString $ w

possWordAsString :: Token -> String
possWordAsString = either (view _Wrapped) (Te.unpack . view (_parsedW._WordIdentifier)) . view tokenIso

parseUnknown :: String -> CheckerM Unknown
parseUnknown n = do
  (UnknownToken unknown) <- satisfy' (== UnknownToken (Unknown n))
  return unknown

sealed :: CheckerM x -> CheckerM x
sealed p = do
  oldState <- getState
  result <- p
  putState oldState
  return result
  

is pr = isRight . matching pr

liftUp = lift . lift

-- showEffs'' =  mapM (iop . (\(c,e) -> render $ stackEffect c $+$ stackEffect e))
-- showEffs' =  mapM (iop . render . stackEffect)
-- showEff =  iop . render . stackEffect
