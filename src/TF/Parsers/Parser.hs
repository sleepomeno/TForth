{-# LANGUAGE LambdaCase,OverloadedStrings, TupleSections, DeriveDataTypeable, TypeFamilies, FunctionalDependencies, RecordWildCards, FlexibleContexts, RankNTypes, TemplateHaskell,  DeriveFunctor, NoMonomorphismRestriction, FlexibleInstances #-}

module TF.Parsers.Parser (parseProgram) where

import Prelude hiding (Word)
import           Control.Applicative hiding (optional, (<|>),many)

import Control.Lens hiding (noneOf,(??))
import Lens.Family.Total hiding ((&))
import           Control.Error as E
import  Text.PrettyPrint (render,vcat)
import Control.Arrow (second, first)
import Data.Data
import Data.List
import Data.Monoid
import TF.Evaluator
import           TF.WordsBuilder (buildWord')
import           TF.StackEffectParser (parseFieldType, parseEffect, defParseStackEffectsConfig, parseCast', parseAssertion')
import Control.Monad.Error
import           Control.Monad.State hiding (state)
import           Control.Monad.Reader (local, runReaderT, ask)
import           Control.Monad.Error.Lens
import           Control.Monad.Free
-- import           Control.Monad.Trans.Free
import           Data.Char hiding (Control)
import qualified Data.Map as M
import qualified Data.Set as S
import           TF.Types hiding (state, isSubtypeOf)
import qualified TF.Types as T
import qualified TF.Words as W hiding (coreWords')
import           TF.Checker (checkNodes)
import           TF.CheckerUtils (withEmpty, withEmpty''')
import  TF.Util
import qualified Data.Text as Te
import           Data.Maybe
import           Text.Parsec hiding (runParser, anyToken, (<|>))
import qualified TF.Printer as P
import TF.Errors
import Debug.Trace

import TF.Parsers.OOP
import TF.Parsers.ControlStructures
import TF.Parsers.ParserUtils
import TF.Parsers.Create
import TF.Parsers.Misc

parseProgram :: CheckerM ([Node], ParseState)
parseProgram = do
  coreWords <- lift W.coreWordsByIdentifier :: CheckerM (M.Map Parsable Word)
  wordsMap .= coreWords  
  forthWordsOrExprs <- many parseNode
  st <- getState
  let effs = toListOf (effects._Wrapped._1.traverse._2) st
      allBeforesEmpty :: Bool
      allBeforesEmpty = all (null . view before) effs

  effectsValid <- views topLevelEmpty ((allBeforesEmpty ||) . not)
  if effectsValid then
    return (forthWordsOrExprs, st)
  else
    liftUp $ throwing _UnemptyStack ("Top Level", "'Before's of top level stack effects must be empty!")

parseNode :: CheckerM Node
parseNode = do
  parseNodeWithout []

parseNodeWithout :: [Word] -> CheckerM Node
parseNodeWithout ws = do
  node <- withEmpty $ liftM (new _Expr) expression </> liftM (new _ForthWord) (evalForthWordWithout ws)

  applyTypeChecking node
  return node

applyTypeChecking node = do 
  doTypeChecking <- view typeCheck

  when doTypeChecking $ void $ 
    checkNodes [node]

  
try' expr = lift . try $ (expr `runReaderT` env)
env = ExpressionEnv parseWord isKnownWord parseStackEffectSemantics parseNode parseNodeWithout

expression :: CheckerM Expr
expression = (`runReaderT` env) $ parsePostpone </> try' parseIfElse </> try' parseIf  </> parseColon </> try' parseExecute </> try' parseAssertion </> try' parseCast </>  try' parseTick </> try' parseDoLoop </> try' parseDoPlusLoop </> try' parseBeginUntil </> try' parseBeginWhileRepeat </> parseInterpreted </> try' parseFieldCall </> try' parseMethodCall </> try' parseNewObject </> try' parseSuperclassMethodCall </> try' parseClass </> try' parseNoName </> try' parseCreating  </> try' parseInclude </> try' parseRequire

parseWord :: Te.Text -> CheckerM ParsedWord
parseWord w = do
  coreWords <- use wordsMap
  let maybeWord = M.lookup (new _WordIdentifier w) coreWords
  when (isNothing maybeWord) $ throwing _Impossible $ ("Did not find word " <> (Te.unpack w))
  let w'' = maybeWord ^?! _Just
    
  (Right w') <- satisfy' (== Right w'')
  (KnownWord pw, _) <- evalKnownWord  w' 
  return pw

isKnownWord :: CheckerM (Maybe (Either ForthWord DefOrWord) )
isKnownWord              = do
  possWord <- anyToken
  s        <- getState
  let maybeColonDefinition' :: Unknown -> Maybe ColonDefinition'
      maybeColonDefinition' w'   = preview (definedWords'.at (w' ^. name)._Just._ColonDefinition) s
  maybeDefOrWord <- possWord & (_case & on _Unknown (\uk -> do 
    iopP $ uk ^. name

    runMaybeT $ do
      y <- hoistMaybe $ maybeColonDefinition' uk
      let immediate = y ^. _1.isImmediate
      if immediate then do
        forthWord <- lift $ evalColonDefinition  (y & _1.isImmediate .~ False)
        return $ Left forthWord
      else 
        return $ Right . new _Def $ y ^. _1.name)

    & on _Word (\word ->
      if word ^. isImmediate then do 
        (forthWord, _) <- evalKnownWord (word & isImmediate .~ False)
        return $ Just . Left $ forthWord
      else 
        return $ Just . Right . new _Word $ word))

  iopP $ show maybeDefOrWord
  return maybeDefOrWord
    
parseStackEffectString = do
  local (readFromStream .~ False) $ parseWord "("
  commentBody <- manyTill anyToken (parseUnknown ")") 
  let commentBody' = map possWordAsString commentBody
      result = ("( " ++ ) . (++ " )") . unwords $ commentBody'
  return result

type UnresolvedArgsM = StateT UnresolvedArgsTypesState CheckerM 
  
prepareUnresolvedArgsTypes :: (Semantics, Bool) -> CheckerM (Semantics, Bool)
prepareUnresolvedArgsTypes (sem, forced) = do
  effs <- (`evalStateT` UnresolvedArgsTypesState M.empty) $ forM (sem ^. (effectsOfStack._Wrapped)) go
  return (sem & effectsOfStack._Wrapped .~ effs, forced)
  where

    go :: StackEffect -> UnresolvedArgsM StackEffect
    go eff = do
      bs <- mapM indexedStackType' $ eff ^. before
      args <- mapM definingOrNot $ eff ^. streamArgs
      as <- mapM indexedStackType' $ eff ^. after
      return $ eff & streamArgs .~ args & before .~ bs & after .~ as

    definingOrNot :: DefiningOrNot -> UnresolvedArgsM DefiningOrNot
    definingOrNot = \case
      -- arg@(Left DefiningArg{}) -> return arg
      arg@(Right (StreamArg _ _ _ (Just (UnknownR index)))) -> do
        newIndex <- getIndex index
        return $ arg & _Right.runtimeSpecified._Just._UnknownR .~ newIndex
      arg -> return arg
            
    indexedStackType' :: IndexedStackType -> UnresolvedArgsM IndexedStackType
    indexedStackType' (arg@(NoReference (ExecutionType (ExecutionToken _ (Just (UnknownR index))))), i) = do
      newIndex <- getIndex index
      return (arg & _NoReference._ExecutionType.runtimeSpecified._Just._UnknownR .~ newIndex, i)
    indexedStackType' x = return x

    getIndex index = do 
      index' <- use (indexToIdentifier.at index)  :: UnresolvedArgsM (Maybe Int)
      case index' of
        Just index'' -> return index''
        Nothing      -> do
          uniqueIdentifier <- lift $ identifier <<+= 1
          indexToIdentifier.at index ?= uniqueIdentifier
          return uniqueIdentifier
      
parseStackEffectSemantics :: (String -> ParseStackEffectsConfig -> Script' ParseEffectResult) -> CheckerM (Semantics, Bool)
parseStackEffectSemantics p = do
  stackEffect' <- parseStackEffectString   :: CheckerM String
  iop $ "stackeffect-string:"
  iop $ stackEffect'

  classes' <- views classInterfaces (map fst . M.toList) <$> getState
  classes'' <- views classFields (map fst . M.toList) <$> getState
  dynamic <- view allowDynamicInStackComments
  effect''' <- handling _ParseErr' (unexpected . show) (lift $ p stackEffect' (defParseStackEffectsConfig & classNames .~ (classes' ++ classes'') & allowDynamicInStackComments .~ dynamic ))
  let effect' = getSemantics effect'''
  prepareUnresolvedArgsTypes effect'
  where
    getSemantics :: ParseEffectResult -> (Semantics, Bool)
    getSemantics result = let streamArgs = view streamArguments result

                              effects' =  view parsedEffects result & traverse %~ (\(b,a) -> StackEffect (reverse b) streamArgs (reverse a))
                     in
                       (def :: Semantics) & effectsOfStack._Wrapped .~ effects'  & (, result ^. forcedEffect)

