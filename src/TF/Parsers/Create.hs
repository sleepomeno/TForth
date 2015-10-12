{-# LANGUAGE OverloadedStrings,  TypeFamilies  #-}


module TF.Parsers.Create where


import Control.Lens hiding (noneOf,(??))
import           Control.Error as E
import TF.Evaluator
import           Control.Monad.State hiding (state)
import           Control.Monad.Error.Lens
-- import           Control.Monad.Trans.Free
import qualified Data.Map as M
import           TF.Types hiding (state, isSubtypeOf)
import           TF.CheckerUtils (withEmpty)
import  TF.Util
import           Text.Parsec hiding (runParser, anyToken)
import TF.Errors

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
  let commaDoes = mapMaybe (\w -> M.lookup (new _WordIdentifier w) coreWords) [",",  "does>"]
  let forbidden = commaDoes ++ forbidden'
  parseNodeWithout <- view parseNodeWithout'
  parseWord <- view parseWord'
  env <- ask
  handling _UnknownWord (lift . unexpected) $ lift $ withEmpty $ (,) <$> many (parseNodeWithout forbidden) <*> ((new _ForthWord . KnownWord) <$> parseWord ",")
