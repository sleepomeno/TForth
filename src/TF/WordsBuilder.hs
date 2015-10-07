{-# LANGUAGE TupleSections, RecordWildCards, FlexibleContexts, RankNTypes, TemplateHaskell,  DeriveFunctor, NoMonomorphismRestriction, FlexibleInstances #-}

module TF.WordsBuilder where

import Prelude hiding (until, drop, Word)
import           Control.Lens 
import Control.Applicative
import           Control.Error
import           TF.ForthTypes as FT
import           Control.Monad
import           Control.Monad.Reader
-- import           Control.Monad.Trans.Free
import           Control.Monad.Trans.State hiding (state)
import           Control.Monad.Free
-- import           Control.Monad.State hiding (state)
import Control.Arrow (second)
import           TF.StackEffectParser (parseEffect, defParseStackEffectsConfig)
import qualified Data.Text as Te
import           TF.Types 


type BuildMonad = ReaderT ParseConfig (StateT BuildState Script')

updateSemantics :: Traversal' Optional b -> (b -> b) -> BuildMonad ()
updateSemantics l' modSem = do
  state' <- use state
  let l = semanticLens state' :: Traversal' Word Optional 
  word.l.l' %= modSem
  
                               
setSemantics' :: Traversal' Optional b -> b -> BuildMonad ()
setSemantics' l' sem = updateSemantics l' (const sem)

semanticLens :: SemanticsState -> Traversal' Word Optional 
semanticLens INTERPRETATION = interpretation._IntSemDefined
semanticLens COMPILATION = compilation._CompSemDefined
semanticLens EXECUTION = execution._Wrapped
semanticLens RUNTIME = runtime._Wrapped

addInfo (EFFECT_UNDEFINED c) = do
  setSemantics' id Undefined
  c

addInfo (COMPILATION_START c) = do
  state .= COMPILATION
  word.compilation .= CompSemDefined (Sem def)
  c

addInfo (RUNTIME_START c) = do
  state .= RUNTIME
  word.runtime .= RunSem (Sem def)
  c

addInfo (INTERPRETATION_START c) = do
  state .= INTERPRETATION
  word.interpretation .= IntSemDefined (Sem def)
  c

addInfo (COMPILATION_END c) = state .= EXECUTION >> c

addInfo (INTERPRETATION_END c) = state .= EXECUTION >> c

addInfo (RUNTIME_END c) = state .= EXECUTION >> c

addInfo (EFFECT e c) = do
  parseResult <- lift . lift $ parseEffect e defParseStackEffectsConfig
  let streamArgs' = view streamArguments parseResult
      effects' =  view parsedEffects parseResult & traverse %~ (\(b,a) -> StackEffect b streamArgs' a)
      isIntersect = view isIntersection parseResult
  st' <- use state
  if st' == EXECUTION then
    word.intersectionType.execEffect .= isIntersect
  else
    word.intersectionType.compileEffect .= isIntersect

  shouldDoDynTransform <- view allCoreDynamic
  let effects'' = if shouldDoDynTransform then
                    ((effects' & traverse.before.traverse._1 %~ setBaseType Dynamic
                             & traverse.after.traverse._1 %~ setBaseType Dynamic) :: [StackEffect])
                             & traverse.streamArgs.traverse._Defining.argType._Just._1 %~ setBaseType Dynamic
                  else
                    effects'
  effects''' <- addTypeIndices effects''
  setSemantics' (_Sem.effectsOfStack._Wrapped) effects'''
  c

addInfo (END) = return ()

addInfo (DESCRIPTION d' c) = do
  setSemantics' (_Sem.(FT.description)) d'
  c

addInfo (NAME n' c) = word.name .= n'  >> c
addInfo (ENTER s c) = do
  setSemantics' (_Sem.TF.Types.enter) (Just s)
  c

addInfo (IMMEDIATE c) = word.isImmediate .= True  >> c
addInfo (PARSED_STR p c) = word.parsed .= Left p  >> c
addInfo (PARSED_NUM c) = word.parsed .= Right ()  >> c
         
addTypeIndices effects = do
  transformedEffects <- do
    let addTypeIndex Nothing = do
          newId <- lift . lift $ identifier <<+= 1
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

buildWord :: Free WordDefinition a -> Free WordDefinition a
buildWord = id

buildWord' :: Free WordDefinition a -> Script' BuildState
buildWord' w = do
  conf <- ask
  (`execStateT` def) $ flip runReaderT conf $ (iterM (addInfo) (w >> liftF END))  >> postProcess

postProcess :: BuildMonad () 
postProcess = do
  int <- use (word.interpretation)
  comp <- use (word.compilation)
  when (int ^?! _IntSemDefined == NotSet) $
    word.interpretation .= ADOPT_EXECUTION
  when (comp ^?! _CompSemDefined == NotSet) $ do
    immediate' <- use $ word.isImmediate
    word.compilation .= if immediate' then IMMEDIATE_EXECUTION else APPEND_EXECUTION
  wordName <- use (word.name)
  wordParsed <- use (word.parsed._Left)
  when (null wordName) $
     word.name .= Te.unpack wordParsed
