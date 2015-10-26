{-# LANGUAGE MultiWayIf, LambdaCase, TupleSections, FlexibleContexts   #-}

module TF.Evaluator (
    evalForthWordWithout
  , evalKnownWord
  , evalColonDefinition
  , evalUnknown
  ) where

import Prelude hiding (Word, last)

import Control.Lens hiding (noneOf,(??), children)

import Data.Monoid (getAny)
import Data.Text.Lens 
import Lens.Family.Total hiding ((&))
import           Control.Monad.Cont
import qualified Data.Text as Te
import           Control.Error as E
import  Text.PrettyPrint (render)
import           Control.Monad.Reader (local)
import           Control.Monad.Error.Lens
import           Data.Monoid ((<>))
import           TF.SubtypeUtil
import           TF.Types hiding (state)
import qualified Data.Map as M
import  TF.Util
import Control.Arrow (first)
import           Data.Maybe
import           Text.Parsec hiding (runParser, anyToken)
import qualified TF.Printer as P
import TF.Errors

import TF.Parsers.ParserUtils (withTrace,withTrace')
import TF.Type.StackEffect
import TF.Type.Nodes



evalToken :: Token -> CheckerM (ForthWord, SemState)
evalToken (UnknownToken x) =  evalUnknown x
evalToken (WordToken x ) = evalKnownWord x
  
-- |Parses a Token - when it's a unknown check if there is a definition. If the definition is immediate, we are in compile-mode and it contains postpones we need to prepend the body of the definition to the current stream
evalForthWordWithout       :: [Word]     -> CheckerM ForthWord
evalForthWordWithout ws         = do
            possWord                       <- noneOf' (map WordToken ws)
            (w,st) <- possWord & evalToken

            modifyState (set _stateVar st)
            return w

            
-- | Determines the semantics of the word, according to the state and determines whether its gets compiled or executed. The word can change the state variable.
evalKnownWord                                       :: Word -> CheckerM  (ForthWord, SemState)
evalKnownWord w'@(Word _ nameW runtime execution compSem intSem _ intersect) = do 
  s <- getState
  let state'               = view _stateVar s
  let definedExeSem        = w' ^. _execution._Wrapped ^? _Sem :: Maybe Semantics
      runtimeSem           = w' ^. _runtime._Wrapped ^? _Sem   :: Maybe Semantics

  sem <- if state' == INTERPRETSTATE then
              case intSem of
                ADOPT_EXECUTION        -> return definedExeSem
                IntSemDefined (Sem x)  -> return . Just $ x
                _                      -> unexpected $ "Interpretation semantics not defined for " ++ (w' ^. _nameW)
            else
              case compSem of
                IMMEDIATE_EXECUTION    -> return  definedExeSem
                CompSemDefined (Sem x) -> return . Just $ x
                APPEND_EXECUTION       -> return definedExeSem
                _                      -> unexpected $ "Compilation semantics not defined" ++ (w' ^. _nameW)
              

  modifyState (_stateVar .~ fromMaybe state' (sem >>= view _semEnter))

  let reverseStacks' = reverseArgs
                        
      reverseStacks sem' = (`fmap` sem') reverseArgs
                                           
      _semToArgs = _semEffectsOfStack._stefwiMultiEffects._Wrapped.traverse
      reverseArgs = over (_semToArgs._before) reverse .
                    over (_semToArgs._after) reverse .
                    over (_semToArgs._streamArgs) reverse
      singleSemantics ::   CompiledExecutedOrBoth MultiStackEffect
      singleSemantics = (view (_semEffectsOfStack._stefwiMultiEffects) . fromJust $ reverseStacks sem) &
                           if state' == COMPILESTATE && compSem == APPEND_EXECUTION then
                             One' 
                           else 
                             maybe Two' (\runtime execSem -> Three' (view (_semEffectsOfStack._stefwiMultiEffects) . reverseArgs $ runtime, execSem)) runtimeSem

  let newIntersect = if | state' == COMPILESTATE && compSem == APPEND_EXECUTION -> intersect & _compileEffect .~ (intersect ^. _execEffect)
                        | isNothing runtimeSem -> intersect
                        | True -> intersect

  let kw = ParsedWord (w' ^. _parsedW) nameW singleSemantics (view _semEnter (fromJust sem)) newIntersect 

  let args :: MaybeT (ParsecT [Token] ParseState StackEffectM) [DefiningOrNot]
      args = hoistMaybe $ preview (_stacksEffects._ExecutedEff._Wrapped._head._streamArgs) kw `mplus`
                          preview (_stacksEffects._CompAndExecutedEff._2._Wrapped._head._streamArgs) kw 
      resolveArgs = do
          rFS <- view readFromStream
          guard rFS
          args' <- args
          resolvedArgs <- lift (resolveStreamArgs args' []) :: MaybeT (ParsecT [Token] ParseState StackEffectM) [DefiningOrNot]
          let resolvedRuntimes = resolvedArgs ^.. traverse._NotDefining._runtimeSpecified._Just._ResolvedR :: [(UniqueArg, StackEffect)]
          return $ kw & _stacksEffects._ExecutedEff._Wrapped.traverse %~ ((_streamArgs .~ resolvedArgs) . (_before.traverse %~ resolveRuntimeType resolvedRuntimes) . (_after.traverse %~ resolveRuntimeType resolvedRuntimes))

  kw' <- runMaybeT resolveArgs

  s <- getState
  return (KnownWord (maybe kw id kw'), view _stateVar s)
          

  

maybeColonDefinition :: Unknown -> ParseState -> Maybe ColonDefinitionProcessed
maybeColonDefinition w' s   = preview (_definedWords'.at (w' ^. _Wrapped)._Just._ColDef) s
evalNonDefinition  =  UnknownE . Unknown . view _Wrapped

evalColonDefinition :: ColonDefinitionProcessed -> CheckerM ForthWord
evalColonDefinition (ColonDefinitionProcessed colonDef effs')  = do
  s <- getState
  
  let (ColonDefinition _ (ColonDefinitionMeta colonName isCdefImmediate)) = colonDef
  let st = view _stateVar s
      executed = st == INTERPRETSTATE || isCdefImmediate
      
  typeCheckingEnabled <- view typeCheck

  when typeCheckingEnabled $ void $ runExceptT $ do
    cause <- hoistEither $ matching _Failed effs'
    lift $ throwing _ClashInWord $ "ERROR in '" <> colonName <> "': " <> cause

  let effs = [emptySt] `fromMaybe` ((effs' ^? _Checked._stefwiMultiEffects._Wrapped) `mplus` (effs' ^? _Forced._stefwiMultiEffects._Wrapped))

  stEff <- liftUp $ tryHead (_Impossible # (colonName ++ " has no effects! Empty List!")) effs

  let intersect = getAny $ effs' ^. (_forcedOrChecked._stefwiIntersection._Wrapped._Unwrapped)

  let args = stEff ^. _streamArgs
      compiledOrExecuted = if executed  then
                             Executed
                           else
                             Compiled

  newEffects <- if executed then do
              resolvedArgs <- resolveStreamArgs args []
              let resolvedRuntimes = resolvedArgs ^.. traverse._NotDefining._runtimeSpecified._Just._ResolvedR :: [(UniqueArg, StackEffect)]
              return $ effs & (traverse._streamArgs .~ resolvedArgs ) & (traverse._before.traverse) %~ (resolveRuntimeType resolvedRuntimes) & (traverse._after.traverse) %~ (resolveRuntimeType resolvedRuntimes)

           else
              return effs



  return $ DefE . compiledOrExecuted . (, (StackEffectsWI (MultiStackEffect newEffects) (Intersection intersect))) $ colonName

evalCreatedWord :: Unknown -> MaybeT CheckerM (ForthWord, SemState)
evalCreatedWord (Unknown ukName) = do
  parseState <- lift getState
  let maybeEffects :: Maybe [StackEffect]
      maybeEffects = preview (_definedWords'.at ukName._Just._CreateDef) parseState 
  effs <- hoistMaybe maybeEffects
  let st = view _stateVar parseState
      executed = st == INTERPRETSTATE 

  let compiledOrExecuted = if executed  then
                             Executed
                           else
                             Compiled

  return (DefE . compiledOrExecuted . (, StackEffectsWI (MultiStackEffect effs) def) $ ukName, st)

  
evalDefinedWord :: Unknown -> MaybeT CheckerM (ForthWord, SemState)
evalDefinedWord uk = do
                      
     s <- lift getState
     let state' = view _stateVar s
     cDef@(ColonDefinitionProcessed definition effects) <- hoistMaybe $ maybeColonDefinition uk s

     lift $ when (isImmediateColonDefinition definition) $ do
               input <- getInput
               coreWords <- use _wordsMap
               let lookupW w = fromJust $ M.lookup (WordIdentifier (Te.pack w)) coreWords
               let defOrWords' :: [Either NameOfDefinition NameOfWord]
                   defOrWords' = definition ^.. body.traverse._Expr._Postpone
                   defOrWords :: [Either NameOfDefinition Word]
                   defOrWords = defOrWords' & traverse._Right %~ lookupW
                   postpones :: [Token]
                   postpones = defOrWords & map
                               (either (UnknownToken . Unknown)
                                       WordToken) 
               setInput (postpones ++ input)
     forthWord <- lift $ evalColonDefinition cDef -- state'
     return (forthWord, state')


            
evalUnknown :: Unknown -> CheckerM (ForthWord, SemState)
evalUnknown uk =  do
  s <- getState
  fmap fromJust . runMaybeT $ msum [evalDefinedWord uk, evalCreatedWord uk, return (evalNonDefinition uk, view _stateVar s)]

handleHOTstreamArgument :: DefiningOrNot -> Token -> CheckerM DefiningOrNot
handleHOTstreamArgument arg@(NotDefining (StreamArg (ArgInfo _ _ _ ) (Just (UnknownR index)))) token = do 
  (forthWord, _) <- sealed $ local (readFromStream .~ False) $ evalToken token
  case forthWord of
    UnknownE _ -> return arg
    DefE definition -> do
      let effs = definition ^. compOrExecIso.chosen._2._stefwiMultiEffects._Wrapped :: [StackEffect]
      adjustHOT effs
    KnownWord pw -> do
      when (has (_stacksEffects._CompAndExecutedEff) pw) $
        throwing _StreamArgHasExecAndCompEffect ()
      let effs =  view (_stacksEffects._ExecutedEff._Wrapped) pw
               ++ view (_stacksEffects._CompiledEff._Wrapped) pw :: [StackEffect]
      adjustHOT effs
  where
    adjustHOT effs = do
      unless (length effs == 1) $ throwing _MultiHigherOrderArg () 
      let eff = head effs :: StackEffect

      s <- getState
      let eff' = view (_unresolvedArgsTypes.at index) s :: Maybe StackEffect

      case eff' of
        Just eff'' -> do
          isSubtype <- eff `effectIsSubtypeOf` eff''
          unless isSubtype $ lift $ throwing _HOTNotSubtype ()
          return $ arg & _NotDefining._runtimeSpecified ?~ ResolvedR index eff''
        Nothing    -> do
          let newState = s & (_unresolvedArgsTypes.at index) ?~ eff
          putState newState
          return $ arg & _NotDefining._runtimeSpecified ?~ ResolvedR index eff
  

handleHOTstreamArgument arg@(NotDefining (StreamArg (ArgInfo _ _ _ )(Just (KnownR effs)))) possWord = do 
  return arg

handleHOTstreamArgument arg _ = return arg

resolveStreamArgs :: [DefiningOrNot] -> [DefiningOrNot] -> CheckerM [DefiningOrNot]
resolveStreamArgs [] acc = return acc
resolveStreamArgs (x:xs) acc =  do
    -- let delimiter = x & (_case & on _Defining (view $ _definingArgInfo._endDelimiter) & on _NotDefining (view $ _streamArgInfo._endDelimiter))
    let delimiter = case x of
          Defining x -> x ^. _definingArgInfo._endDelimiter
          NotDefining x -> x ^. _streamArgInfo._endDelimiter
        parseArgument :: Maybe String -> CheckerM (String, DefiningOrNot)
        parseArgument = \case
          Nothing  -> (do
            w <- anyToken :: CheckerM Token
            case w of 
                uk@(UnknownToken (Unknown name)) -> do
                    x' <- handleHOTstreamArgument x uk
                    return (name, x')
                WordToken (Word Number _ _ _ _ _ _ _) -> throwing _NumberAsStreamArg ()
                knownWord@(WordToken w) -> do
                  x' <- handleHOTstreamArgument x knownWord
                  return (w ^?! (_parsedW._WordIdentifier.unpacked), x'))
          Just endDelimiter -> do
            result <- unwords <$> manyTill getNextParameter (parseUnknown endDelimiter)
            return (result, x)
    
    (resolveArg, x) <- parseArgument delimiter

    let x' :: DefiningOrNot
        x' = x & _Defining._definingArgInfo._resolved ?~ resolveArg
               & _NotDefining._streamArgInfo._resolved ?~ resolveArg 

    resolveStreamArgs xs (x':acc)

