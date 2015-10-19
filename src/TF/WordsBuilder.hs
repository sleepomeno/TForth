{-# LANGUAGE TupleSections,  FlexibleContexts, RankNTypes,  NoMonomorphismRestriction  #-}

module TF.WordsBuilder where

import Prelude hiding (until, drop, Word)
import           Control.Lens 
import           TF.ForthTypes as FT
import           Control.Monad
import           Control.Monad.Reader
-- import           Control.Monad.Trans.Free
import           Control.Monad.Trans.State hiding (state)
import           Control.Monad.Free
-- import           Control.Monad.State hiding (state)
import           TF.StackEffectParser (parseEffect, defParseStackEffectsConfig)
import qualified Data.Text as Te
import           TF.Types 
import TF.HandleDegrees

import TF.Type.StackEffect
import TF.Type.Nodes


type BuildMonad = ReaderT ParseConfig (StateT BuildState Script')

updateSemantics :: Traversal' Optional b -> (b -> b) -> BuildMonad ()
updateSemantics l' modSem = do
  state' <- use state
  let l = semanticLens state' :: Traversal' Word Optional 
  word.l.l' %= modSem
  
                               
setSemantics' :: Traversal' Optional b -> b -> BuildMonad ()
setSemantics' l' sem = updateSemantics l' (const sem)

semanticLens :: SemanticsState -> Traversal' Word Optional 
semanticLens INTERPRETATION = _interpretation._IntSemDefined
semanticLens COMPILATION = _compilation._CompSemDefined
semanticLens EXECUTION = _execution._Wrapped
semanticLens RUNTIME = _runtime._Wrapped

addInfo (EFFECT_UNDEFINED c) = do
  setSemantics' id Undefined
  c

addInfo (COMPILATION_START c) = do
  state .= COMPILATION
  word._compilation .= CompSemDefined (Sem def)
  c

addInfo (RUNTIME_START c) = do
  state .= RUNTIME
  word._runtime .= RunSem (Sem def)
  c

addInfo (INTERPRETATION_START c) = do
  state .= INTERPRETATION
  word._interpretation .= IntSemDefined (Sem def)
  c

addInfo (COMPILATION_END c) = state .= EXECUTION >> c

addInfo (INTERPRETATION_END c) = state .= EXECUTION >> c

addInfo (RUNTIME_END c) = state .= EXECUTION >> c

addInfo (EFFECT e c) = do
  ParseEffectResult parsedEffects streamArgs forced isIntersect <- lift . lift $ parseEffect e defParseStackEffectsConfig
  let effects' =  parsedEffects & traverse %~ (\(b,a) -> StackEffect b streamArgs a)
  st' <- use state
  if st' == EXECUTION then
    word._intersections._execEffect .= isIntersect
  else
    word._intersections._compileEffect .= isIntersect

  shouldDoDynTransform <- view allCoreDynamic
  let effects'' = if shouldDoDynTransform then
                    ((effects' & traverse._before.traverse._1 %~ setBaseType Dynamic
                             & traverse._after.traverse._1 %~ setBaseType Dynamic) :: [StackEffect])
                             & traverse._streamArgs.traverse._Defining._argType._Just._1 %~ setBaseType Dynamic
                  else
                    effects'
  effects''' <- addTypeIndices effects''
  setSemantics' (_Sem._semEffectsOfStack._Wrapped) effects'''
  c

addInfo (END) = return ()

addInfo (DESCRIPTION d' c) = do
  setSemantics' (_Sem._semDescription) d'
  c

addInfo (NAME n' c) = word._nameW .= n'  >> c
addInfo (ENTER s c) = do
  setSemantics' (_Sem._semEnter) (Just s)
  c

addInfo (IMMEDIATE c) = word._isImmediateWord .= True  >> c
addInfo (PARSED_STR p c) = word._parsedW .= WordIdentifier p  >> c
addInfo (PARSED_NUM c) = word._parsedW .= Number  >> c
         
addTypeIndices effects = do
  transformedEffects <- do
    let addTypeIndex Nothing = do
          newId <- lift . lift $ _identifier <<+= 1
          return $ Just newId
        addTypeIndex x = return x
          
    forM effects $ \(StackEffect before args after) -> do
      before' <- forM before $ \(t, i) -> (t,) <$> addTypeIndex i
      after' <- forM after $ \(t, i) -> (t,) <$> addTypeIndex i
      return (StackEffect before args after)
      
  return transformedEffects
  
  
parsing :: Te.Text -> Free WordDefinition ()
parsing n' = liftF $ PARSED_STR n' ()
numberParsed = liftF $ PARSED_NUM ()
named n' = liftF $ NAME n' ()
describing descr = liftF $ DESCRIPTION descr ()
effect eff = liftF $ EFFECT eff ()
  

immediate = liftF $ IMMEDIATE ()
compilationStart = liftF $ COMPILATION_START ()
compilationEnd = liftF $ COMPILATION_END ()
runtimeStart = liftF $ RUNTIME_START ()
runtimeEnd = liftF $ RUNTIME_END ()
compileComing = liftF $ COMPILE_COMING ()
interpretationStart = liftF $ INTERPRETATION_START ()
interpretationEnd = liftF $ INTERPRETATION_END ()
undefinedEffect = liftF $ EFFECT_UNDEFINED ()
entering s = liftF $ ENTER s ()

undefinedInterpretation = interpretationStart >> undefinedEffect >> interpretationEnd

buildWord' :: Free WordDefinition a -> Script' BuildState
buildWord' w = do
  conf <- ask
  (`execStateT` def) $ flip runReaderT conf $ (iterM (addInfo) (w >> liftF END))  >> postProcess

postProcess :: BuildMonad () 
postProcess = do
  int <- use (word._interpretation)
  comp <- use (word._compilation)
  when (int ^?! _IntSemDefined == NotSet) $
    word._interpretation .= ADOPT_EXECUTION
  when (comp ^?! _CompSemDefined == NotSet) $ do
    immediate' <- use $ word._isImmediateWord
    word._compilation .= if immediate' then IMMEDIATE_EXECUTION else APPEND_EXECUTION
  wordName <- use (word._nameW)
  wordParsed <- use (word._parsedW._WordIdentifier)
  when (null wordName) $
     word._nameW .= Te.unpack wordParsed
