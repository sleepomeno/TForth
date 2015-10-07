{-# LANGUAGE LambdaCase,OverloadedStrings, TupleSections, DeriveDataTypeable, TypeFamilies, FunctionalDependencies, RecordWildCards, FlexibleContexts, RankNTypes, TemplateHaskell,  DeriveFunctor, NoMonomorphismRestriction, FlexibleInstances #-}


module TF.Parsers.Create where

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
import           Control.Monad.Reader (local)
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
import           TF.CheckerUtils (withEmpty)
import  TF.Util
import qualified Data.Text as Te
import           Data.Maybe
import           Text.Parsec hiding (runParser, anyToken)
import qualified TF.Printer as P
import TF.Errors
import Debug.Trace

import Control.Monad.Reader

import TF.Parsers.ParserUtils

parseCreating :: ExpressionsM Expr
parseCreating = do

  iop $ "In create"
  let parseUnknown' :: CheckerM (ForthWord, DefiningArg)
      parseUnknown' = do
         (Left uk@(Unknown _)) <- (satisfy' isLeft)
         -- iopP $ "Is an unknown named " ++ (view name uk)
         (forthWord, newState) <- evalUnknown uk
         modifyState (set stateVar newState)

         -- iopP $ render . P.forthWord $ forthWord
         unless (is _DefE forthWord) $ fail "not a defE"

         let (_, effs) = forthWord ^?! (_DefE.chosen)
         let defArg :: Maybe DefiningArg
             defArg = preview (_head.streamArgs.traverse._Defining) effs

         when (isNothing defArg) $ fail "no defining args"
         -- iopP $ "after eval"

         return (forthWord, defArg ^?! _Just)

      parseCreate :: ExpressionsM (ForthWord, DefiningArg)
      parseCreate = do
        pw <- parseWordCreate
        let effs = toListOf (stacksEffects._CompiledEff._Wrapped.traverse) pw  ++ (toListOf (stacksEffects._ExecutedEff._Wrapped.traverse) pw)
            defArg :: Maybe DefiningArg
            defArg = preview (_head.streamArgs.traverse._Defining) effs


        return (KnownWord pw, defArg ^?! _Just)

  (creatingWord, definingArg) <- (lift $ try parseUnknown') </> parseCreate

  -- iopP $ "has streamarguments: "
  -- liftIO . mapM (putStrLn . show) $ streamArguments'
  -- iopP $ "hallo?"

  -- TODO only parse init if no argType has been specified so far (Nothing)
  env <- ask

  let betwe :: CheckerM ([Node], Node)
      betwe = (`runReaderT` env) $ parseStoringValue 
  maybeInitialization <- lift $ optionMaybe $ try $ (`runReaderT` env) $ parseStoringValue 

  -- iop "IN between"
  -- TODO only parse does if no runtimetype has been specified so far (Nothing)
  maybeDoes <- lift $ withEmpty $ optionMaybe $ (`runReaderT` env) parseDoes

  -- let createExpr = Create (new _ForthWord creatingWord) maybeInitialization maybeDoes
  let createExpr = Create (new _ForthWord creatingWord) maybeInitialization maybeDoes
  iop $ "Out create"
  return createExpr

parseDoes = do
  parseWordDoes
  forbidden' <- forbiddenInBranch

  manyWordsTillExcludingWithout ";" forbidden'

parseStoringValue  = do
  forbidden' <- forbiddenInBranch
  coreWords <- lift $ use wordsMap
  let commaDoes = catMaybes $ map (\w -> M.lookup (new _WordIdentifier w) coreWords) [",",  "does>"]
  let forbidden = commaDoes ++ forbidden'
  parseNodeWithout <- view parseNodeWithout'
  parseWord <- view parseWord'
  env <- ask
  handling _UnknownWord (lift . unexpected) $ lift $ withEmpty $ (,) <$> many (parseNodeWithout forbidden) <*> ((new _ForthWord . KnownWord) <$> parseWord ",")
