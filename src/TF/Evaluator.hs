{-# LANGUAGE MultiWayIf, LambdaCase, TupleSections, FlexibleContexts   #-}

module TF.Evaluator (
    evalForthWordWithout
  , evalKnownWord
  , evalColonDefinition
  , evalUnknown
  ) where

import Prelude hiding (Word, last)

import Control.Lens hiding (noneOf,(??), children)

import Data.Text.Lens 
import Lens.Family.Total hiding ((&))
import           Control.Monad.Cont
import           Control.Error as E
import  Text.PrettyPrint (render)
import           Control.Monad.Reader (local)
import           Control.Monad.Error.Lens
import           Data.Monoid ((<>))
import           TF.SubtypeUtil
import           TF.Types hiding (state)
import  TF.Util
import           Data.Maybe
import           Text.Parsec hiding (runParser, anyToken)
import qualified TF.Printer as P
import TF.Errors



evalToken :: Token -> CheckerM (ForthWord, SemState)
evalToken = _case & on _Word evalKnownWord & on _Unknown evalUnknown

  
evalForthWord                   = evalForthWordWithout []

-- |Parses a Token - when it's a unknown check if there is a definition. If the definition is immediate, we are in compile-mode and it contains postpones we need to prepend the body of the definition to the current stream
evalForthWordWithout       :: [Word]     -> CheckerM ForthWord
evalForthWordWithout ws         = do
            possWord                       <- noneOf' (map Right ws)
            (w,st) <- possWord & evalToken

            modifyState (set stateVar st)
            return w

-- | Determines the semantics of the word, according to the state and determines whether its gets compiled or executed. The word can change the state variable.
evalKnownWord                                       :: Word -> CheckerM  (ForthWord, SemState)
evalKnownWord w' = do 
  s <- getState
  let state'               = view stateVar s
  let intSem               = w'^.interpretation               :: InterpretationSemantics
      compSem              = w'^.compilation                  :: CompilationSemantics
      definedExeSem        = w' ^. execution._Wrapped ^? _Sem :: Maybe Semantics
      runtimeSem           = w' ^. runtime._Wrapped ^? _Sem   :: Maybe Semantics
      intersect = w' ^. intersectionType

  -- when (intersect ^. execEffect) $ undefined

  sem <- if state' == INTERPRETSTATE then
              case intSem of
                ADOPT_EXECUTION        -> return definedExeSem
                IntSemDefined (Sem x)  -> return . Just $ x
                _                      -> unexpected $ "Interpretation semantics not defined for " ++ view name w'
            else
              case compSem of
                IMMEDIATE_EXECUTION    -> return  definedExeSem
                CompSemDefined (Sem x) -> return . Just $ x
                APPEND_EXECUTION       -> return definedExeSem
                _                      -> unexpected $ "Compilation semantics not defined" ++ w' ^. name
              

  modifyState (stateVar .~ fromMaybe state' (sem >>= view enter))

  let reverseStacks' = reverseEffects _Wrapped
                        
      reverseStacks sem' = (`fmap` sem') reverseStacks'
                                           
      reverseEffects stack = over (effectsOfStack.stack.traverse.before) reverse .
                             over (effectsOfStack.stack.traverse.after) reverse .
                             over (effectsOfStack.stack.traverse.streamArgs) reverse
      singleSemantics ::   CompiledExecutedOrBoth MultiStackEffect
      singleSemantics = (view effectsOfStack . fromJust $ reverseStacks sem) &
                           if state' == COMPILESTATE && compSem == APPEND_EXECUTION then
                             (_CompiledEff #) 
                           else 
                             maybe (_ExecutedEff #) (\runtime execSem -> (_CompAndExecutedEff #) (view effectsOfStack . reverseStacks' $ runtime, execSem)) runtimeSem

  let newIntersect = if | state' == COMPILESTATE && compSem == APPEND_EXECUTION -> intersect & compileEffect .~ (intersect ^. execEffect)
                        | isNothing runtimeSem -> intersect
                        | True -> intersect

  let kw = ParsedWord {}
           & name .~ view name w'
           & parsed .~ view parsed w'
           & stacksEffects .~ singleSemantics
           & intersectionType .~ newIntersect
           & enter .~ view enter (fromJust sem)

  let args :: MaybeT (ParsecT [Token] ParseState StackEffectM) [DefiningOrNot]
      args = hoistMaybe $ preview (stacksEffects._ExecutedEff._Wrapped._head.streamArgs) kw `mplus`
                          preview (stacksEffects._CompAndExecutedEff._2._Wrapped._head.streamArgs) kw 
      resolveArgs = do
          rFS <- view readFromStream
          guard rFS
          args' <- args
          resolvedArgs <- lift $ resolveStreamArgs args' []
          let resolvedRuntimes = resolvedArgs ^.. traverse._NotDefining.runtimeSpecified._Just._ResolvedR :: [(UniqueArg, StackEffect)]
              -- return $ effs & (traverse.streamArgs .~ resolvedArgs ) & (traverse.before.traverse) %~ (resolveRuntimeType resolvedRuntimes) & (traverse.after.traverse) %~ (resolveRuntimeType resolvedRuntimes)
          return $ kw & stacksEffects._ExecutedEff._Wrapped.traverse %~ ((streamArgs .~ resolvedArgs) . (before.traverse %~ resolveRuntimeType resolvedRuntimes) . (after.traverse %~ resolveRuntimeType resolvedRuntimes))

  kw' <- runMaybeT resolveArgs

  -- iop $ show kw'

  
  s <- getState
  return (KnownWord (maybe kw id kw'), view stateVar s)
  -- return  kw
          

  

maybeColonDefinition :: Unknown -> ParseState -> Maybe ColonDefinition'
maybeColonDefinition w' s   = preview (definedWords'.at (w' ^. name)._Just._ColonDefinition) s-- & fmap (view _ColonDefinition)
-- maybeDefinition w' s   = view (definedWords'.at (w' ^. name)) s
evalNonDefinition  =  UnknownE . Unknown . view name

evalColonDefinition :: ColonDefinition' -> CheckerM ForthWord
evalColonDefinition (colonDef, effs')  = do
  s <- getState
  let st = view stateVar s
      executed = st == INTERPRETSTATE || view isImmediate colonDef
      colonName = colonDef ^. name

  iopP $ "SHOW COLONNAME " ++ colonName
  iopP $ "IS EXECUTED: " ++ show executed

  typeCheckingEnabled <- view typeCheck

  when typeCheckingEnabled $ void $ runExceptT $ do
    cause <- hoistEither $ matching _Failed effs'
    lift $ throwing _ClashInWord $ "ERROR in '" <> colonName <> "': " <> cause

  let effs = [emptySt] `fromMaybe` ((effs' ^? _Checked._1) `mplus` (effs' ^? _Forced))

  stEff <- liftUp $ tryHead (_Impossible # (colonName ++ " has no effects! Empty List!")) effs

  let args = stEff ^. streamArgs
      compiledOrExecuted = if executed  then
                             new _Executed
                           else
                             new _Compiled

  iopP $ "EXECUTED:"
  iopP $ show executed

  effs' <- if executed then do
              resolvedArgs <- resolveStreamArgs args []
              let resolvedRuntimes = resolvedArgs ^.. traverse._NotDefining.runtimeSpecified._Just._ResolvedR :: [(UniqueArg, StackEffect)]
              -- return $ effs & (traverse.streamArgs .~ resolvedArgs ) & (traverse.before.traverse.filtered (\(t, _) -> has (_NoReference._ExecutionType.runtimeSpecified._Just._UnknownR) (baseType' t))) %~ (resolveRuntimeType resolvedRuntimes)
              return $ effs & (traverse.streamArgs .~ resolvedArgs ) & (traverse.before.traverse) %~ (resolveRuntimeType resolvedRuntimes) & (traverse.after.traverse) %~ (resolveRuntimeType resolvedRuntimes)

           else
              return effs
  iopP $ "AFTER resolving"
  mapM_ (iopP . show) $ effs'

  -- logD $ "resolved args: \n" ++ (show effs')



  return $ DefE . compiledOrExecuted . (, effs') . view name $ colonDef

evalCreatedWord :: Unknown -> MaybeT CheckerM (ForthWord, SemState)
evalCreatedWord uk = do
  let ukName = view name uk
  parseState <- lift getState
  -- let maybeEffects = view (colonDefEffects.at ukName) parseState
  let maybeEffects :: Maybe [StackEffect]
      maybeEffects = preview (definedWords'.at ukName._Just._CreateDefinition) parseState 
  effs <- hoistMaybe maybeEffects
  -- iop $ "ukname is '" ++ ukName ++ "'!"
  let st = view stateVar parseState
      executed = st == INTERPRETSTATE 

  let compiledOrExecuted = if executed  then
                             new _Executed
                           else
                             new _Compiled

  return (DefE . compiledOrExecuted . (, effs) $ ukName, st)

  
evalDefinedWord :: Unknown -> MaybeT CheckerM (ForthWord, SemState)
evalDefinedWord uk = do
                      
     s <- lift getState
     let state' = view stateVar s
     cDef@(definition,effects) <- hoistMaybe $ maybeColonDefinition uk s

     -- when (isLeft definition') $
     --     lift $ throwing _ErrorT (definition' ^?! _Left)

     -- let (Right definition) = definition'

     lift $ when (isImmediateColonDefinition definition) $ do
               input <- getInput
               let defOrWords :: [DefOrWord]
                   defOrWords = toListOf (body.traverse._Right._Postpone) definition 
                   postpones :: [Token]
                   postpones = defOrWords & map
                               (either (new _Unknown . Unknown)
                                       (new _Word)) 
               setInput (postpones ++ input)
     forthWord <- lift $ evalColonDefinition cDef -- state'
     return (forthWord, state')


            
evalUnknown :: Unknown -> CheckerM (ForthWord, SemState)
evalUnknown uk =  do
  s <- getState
  fmap fromJust . runMaybeT $ msum [evalDefinedWord uk, evalCreatedWord uk, return (evalNonDefinition uk, view stateVar s)]
  -- fmap fromJust . runMaybeT $ msum [evalDefinedWord uk, evalCreatedWord uk]

handleHOTstreamArgument :: DefiningOrNot -> Token -> CheckerM DefiningOrNot
handleHOTstreamArgument arg@(Right (StreamArg _ _ _ (Just (UnknownR index)))) possWord = do 
  (forthWord, _) <- sealed $ local (readFromStream .~ False) $ evalToken possWord
  iop "handleHOT"
  iop $ show forthWord
  case forthWord of
    UnknownE _ -> return arg
    DefE definition -> do
      let effs = view (chosen._2) definition :: [StackEffect]
      iop "EFF:"
      mapM_ (iopP . render. P.stackEffect) effs
      adjustHOT effs
    KnownWord pw -> do
      when (has (stacksEffects._CompAndExecutedEff) pw) $
        throwing _StreamArgHasExecAndCompEffect ()
      let effs =  view (stacksEffects._ExecutedEff._Wrapped) pw
               ++ view (stacksEffects._CompiledEff._Wrapped) pw :: [StackEffect]
      adjustHOT effs
  where
    adjustHOT effs = do
      unless (length effs == 1) $ throwing _MultiHigherOrderArg () -- TODO eher unnoetig. überprüfe weiter unten bei effectIsSubtypeOf ob jeder effekt ein untertyp von mindestens einem typ im just ist!
      let eff = (effs ^?! _head) :: StackEffect

      iop "THIS IS THE EFF:"
      iop $ render $ P.stackEffect eff
      
      s <- getState
      let eff' = view (unresolvedArgsTypes.at index) s :: Maybe StackEffect

      -- iop $ "eff'"
      -- iop $ show arg

      case eff' of
        Just eff'' -> do
          isSubtype <- eff `effectIsSubtypeOf` eff''
          unless isSubtype $ lift $ throwing _HOTNotSubtype ()
          return $ arg & _NotDefining.runtimeSpecified ?~ ResolvedR index eff''
        Nothing    -> do
          let newState = s & (unresolvedArgsTypes.at index) ?~ eff
          putState newState
          -- TODO why not done?
          return $ arg & _NotDefining.runtimeSpecified ?~ ResolvedR index eff
  

handleHOTstreamArgument arg@(Right (StreamArg _ _ _ (Just (KnownR effs)))) possWord = do 
  return arg

handleHOTstreamArgument arg _ = return arg

resolveStreamArgs :: [DefiningOrNot] -> [DefiningOrNot] -> CheckerM [DefiningOrNot]
resolveStreamArgs [] acc = return acc
resolveStreamArgs (x:xs) acc =  do
    let delimiter = x & (_case & on _Defining (view endDelimiter) & on _NotDefining (view endDelimiter))
        parseArgument :: Maybe String -> CheckerM (String, DefiningOrNot)
        parseArgument = \case
          Nothing  -> (do
            w <- anyToken :: CheckerM Token
            case w of 
                uk@(Left (Unknown name)) -> do
                    x' <- handleHOTstreamArgument x uk
                    return (name, x')
                Right (Word (Right ()) _ _ _ _ _ _ _) -> throwing _NumberAsStreamArg ()
                knownWord@(Right w) -> do
                  x' <- handleHOTstreamArgument x knownWord
                  return (w ^?! (parsed._WordIdentifier.unpacked), x'))
          Just endDelimiter -> do
            result <- unwords <$> manyTill getNextParameter (parseUnknown endDelimiter)
            return (result, x)
    
    (resolveArg, x) <- parseArgument delimiter

    let x' :: DefiningOrNot
        x' = bimap (resolved ?~ resolveArg) (resolved ?~ resolveArg) x

    resolveStreamArgs xs (x':acc)

