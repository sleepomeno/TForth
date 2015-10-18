{-# LANGUAGE OverloadedStrings  #-}

module TF.Parsers.ControlStructures where


import Control.Lens hiding (noneOf,(??))
import           TF.WordsBuilder (buildWord')
import           Control.Monad.State hiding (state)
-- import           Control.Monad.Trans.Free
import           TF.Types hiding (state, isSubtypeOf)
import qualified TF.Types as T
import qualified TF.Words as W

import TF.Parsers.ParserUtils
import TF.Type.StackEffect
import TF.Type.Nodes

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
