{-# LANGUAGE OverloadedStrings  #-}

module TF.Parsers.Misc where

import Control.Lens hiding (noneOf,(??))
import           Control.Error as E
import           TF.StackEffectParser (parseEffect, parseCast', parseAssertion')
import           Control.Monad.State hiding (state)
import           Control.Monad.Error.Lens
import qualified Data.Map as M
import           TF.Types hiding (state, isSubtypeOf)
import  TF.Util
import           Text.Parsec hiding (runParser, anyToken)
import TF.Errors

import Control.Monad.Reader

import TF.Parsers.ParserUtils
import TF.Type.StackEffect
import TF.Type.Nodes

parsePostpone :: ExpressionsM Expr
parsePostpone = do
  env <- ask
  lift $ local (readFromStream .~ False) $ (`runReaderT` env) $ parseWordPostpone
  isKnownWord <- view isKnownWord'
  maybeResult <- lift isKnownWord
  let err   = lift $ unexpected "You can only postpone a known word"
  maybe err (either (return . PostponeImmediate) (return . Postpone)) maybeResult

parseExecute :: ExpressionsM Expr
parseExecute = do
  assert' <- parseAssertion

  parseWordExecute

  -- iop $ "______ EXECUTE ______"

  return $ Execute $ assert' ^?! _Assert._1

parseInclude :: ExpressionsM Expr
parseInclude = do
  parseKeyword "include"
  file <- parseUnknownName
  return $ Include file

parseRequire :: ExpressionsM Expr
parseRequire = do
  parseKeyword "require"
  file <- parseUnknownName
  return $ Require file

parseTick :: ExpressionsM Expr
parseTick = do
  assert' <- parseRawAssertion

  pw <- parseWordTick -- TODO take a tick-like word

  guard $ has (_Assert._1._Compiled) assert'
  guard $ has (stacksEffects._CompiledEff) pw -- TODO _Compiled Or _compiledandexecuted

  iop $ "-------- TICK --------"
  
  return $ Tick (assert' ^. _Assert._1._Compiled) pw

parseInterpreted :: ExpressionsM Expr
parseInterpreted = do
  parseWordLeftBracket
  lift $ modifyState $ set currentCompiling False
  parseNode <- view parseNode'
  expr <- lift $ manyTill parseNode (parseUnknown "]")
  lift $ modifyState $ set currentCompiling True
  lift $ modifyState (stateVar .~ COMPILESTATE)
  return $ Interpreted expr

parseColon :: ExpressionsM Expr
parseColon = do
  -- iop "prse colon"
  parseWordColon
  w <- lift $ possWordAsString <$> anyToken 

  parseStackEffectSemantics <- view parseStackEffectSemantics'
  stackComment <- lift $ optionMaybe $ parseStackEffectSemantics parseEffect
  
  lift $ modifyState $ set currentCompiling True

  let parseColonDefinitionBody :: ExpressionsM (ColonDefinition, [Node])
      parseColonDefinitionBody = do 
        expr <- manyWordsTill ";"
        env <- ask
        maybeImmediate <- lift $ optionMaybe $ flip runReaderT env $ parseWordImmediate
        let isImmediate = isJust maybeImmediate
            colonDefinition = ColonDefinition expr (ColonDefinitionMeta w isImmediate)
        return (colonDefinition, expr)
      createColon (ColonDefinition _ (ColonDefinitionMeta w isImmediate)) = if isImmediate then  ColonExprImmediate else ColonExpr

  let parseBody :: ExpressionsM Expr
      parseBody = do
        (colonDefinition, expr) <- parseColonDefinitionBody 
        lift $ modifyState (over definedWords' $ M.insert w (ColDef (ColonDefinitionProcessed colonDefinition NotChecked)))
        -- modifyState (over definedWords $ M.insert w colonDefinition)
        -- modifyState (lastColonDefinition ?~ w)
        lift $ modifyState $ set currentCompiling False
        return $ (createColon colonDefinition) w stackComment expr

  let typeCheckingFails :: String -> ExpressionsM Expr
      typeCheckingFails reason =  do
        -- iopP $ "failing with reason: " ++ reason

        -- inp <- getInput
        -- mapM_ iopS inp

        allowLocalFailure' <- lift $ view allowLocalFailure
        unless allowLocalFailure' $ throwing _Clash reason
  
        env <- ask
        (colonDefinition, expr) <- lift $ local (typeCheck .~ False) $ flip runReaderT env $ parseColonDefinitionBody
        lift $ modifyState (over definedWords' $ M.insert w (ColDef(ColonDefinitionProcessed colonDefinition (Failed reason))))
        lift $ modifyState $ set currentCompiling False
        return $ ColonExprClash w stackComment

  catches parseBody (errorHandler typeCheckingFails w)

parseCast :: ExpressionsM Expr
parseCast = do
  parseStackEffectSemantics <- view parseStackEffectSemantics'
  (sem, _) <- lift $ parseStackEffectSemantics parseCast'
  iop "CAST"
  iop $ show sem
  let effs = sem ^. _semEffectsOfStack._Wrapped
  compOrExec <- compOrExec'
  return $ Cast (compOrExec effs)

parseAssertion :: ExpressionsM Expr
parseAssertion = do
  iop "TRY ASSERTION"
  -- inputs <- getInput
  -- liftIO $ mapM print inputs

  parseStackEffectSemantics <- view parseStackEffectSemantics'
  (sem, forced) <- lift $ parseStackEffectSemantics parseAssertion'
  iop "ASSERTION"
  -- iop $ show sem
  let effs = sem ^. _semEffectsOfStack._Wrapped
  compOrExec <- compOrExec'
  return $ Assert (compOrExec effs) forced
  
parseRawAssertion :: ExpressionsM Expr
parseRawAssertion = do
  -- iop $ "TRY RAW_ASSERTION"
  parseStackEffectSemantics <- view parseStackEffectSemantics'
  (sem, forced) <- lift $ parseStackEffectSemantics parseEffect
  -- iop $ "RAW_ASSERTION"
  let effs = sem ^. _semEffectsOfStack._Wrapped
  compOrExec <- compOrExec'
  return $ Assert (compOrExec effs) forced
