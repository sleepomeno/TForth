{-# LANGUAGE LambdaCase,OverloadedStrings, TupleSections, DeriveDataTypeable, TypeFamilies, FunctionalDependencies, RecordWildCards, FlexibleContexts, RankNTypes, TemplateHaskell,  DeriveFunctor, NoMonomorphismRestriction, FlexibleInstances #-}

module TF.Parsers.ControlStructures where

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

parseDoLoop :: ExpressionsM Expr
parseDoLoop = do
  parseWordDo
  loopBody <- manyWordsTill "loop"
  return $ ControlExpr $ DoLoop loopBody

parseDoPlusLoop :: ExpressionsM Expr
parseDoPlusLoop = do
  parseWordDo
  loopBody <- manyWordsTill "+loop"
  return $ ControlExpr $ DoPlusLoop loopBody
  
parseIfElse :: ExpressionsM Expr
parseIfElse = do
  parseWordIf
  forbidden <- forbiddenInBranch
  ifExprs   <- manyWordsTillWithout "else" forbidden
  elseExprs <- manyWordsTillWithout "then" forbidden
  return $ ControlExpr $ IfElseExpr ifExprs elseExprs

parseIf :: ExpressionsM Expr
parseIf = do
  parseWordIf
  forbidden <- forbiddenInBranch
  expr <- manyWordsTillWithout "then" forbidden
  return $ ControlExpr $ IfExpr expr

parseBeginUntil :: ExpressionsM Expr
parseBeginUntil = do
  parseWordBegin
  loopBody <- manyWordsTill "until"
  return $ ControlExpr $ BeginUntil loopBody

parseBeginWhileRepeat :: ExpressionsM Expr
parseBeginWhileRepeat = do
  parseWordBegin
  until' <- lift . lift $ view T.word <$> buildWord' W.until
  begins <- manyWordsTillWithout "while" [until'] -- (sequence [view T.word <$> W.until])
  parseWordWhile
  whiles <- manyWordsTill "repeat"
  return $ ControlExpr $ BeginWhileRepeat begins whiles
