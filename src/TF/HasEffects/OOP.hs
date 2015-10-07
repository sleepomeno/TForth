{-# LANGUAGE DeriveDataTypeable, DeriveFunctor, FlexibleContexts,
             FlexibleInstances, FunctionalDependencies, LambdaCase, MultiWayIf,
             NoMonomorphismRestriction, OverlappingInstances, OverloadedStrings,
             RankNTypes, RecordWildCards, TemplateHaskell, TupleSections,
             TypeFamilies #-}

module TF.HasEffects.OOP where

import           Control.Arrow
import Control.Applicative
import           Control.Error            as E
import Control.Monad.Error.Class (MonadError)
import           Control.Lens             hiding (noneOf, (??), _Empty)
import           Control.Monad.Error.Lens
import           Control.Monad.Extra
import           Control.Monad.Reader
import           Control.Monad.Writer
import           Control.Monad.Cont
import           Data.String
-- import           Lens.Family.Total        hiding ((&))
import           Text.PrettyPrint         (Doc, hcat, nest, render, style, text,
                                           vcat, ($+$), (<+>))
import           TF.StackCalculus
import Data.Function (on)
import           TF.StackEffectParser
import           TF.WildcardRules
import           TF.ForthTypes as FT

import           Control.Monad.State
import           Data.Functor
import           Data.List
import           Data.Maybe
import           Data.Monoid
import qualified TF.Types                 as T
import           TF.Util
import           TF.SubtypeUtil
-- import qualified TF.DataTypes as DT
-- import           Data.Data
import qualified Data.Map                 as M
import           Data.Typeable
import           Text.Parsec              hiding (token)
import qualified TF.Printer               as P
import           TF.Types                 hiding (isSubtypeOf, word)
import TF.Errors
import Debug.Trace

import TF.CheckerUtils
import TF.HasEffects.ForthWord

getStackEffects' (NewObject cOrE) = do
    let compOrExec = case cOrE of { Left _ -> new _Compiled ; Right _ -> new _Executed }
        name = case cOrE of { Left x -> x; Right x -> x }
        eff = [StackEffect [] [] [(NoReference $ _ClassType # name, Just 1)]]
    return $ withoutIntersect (effsAsTuples $ (compOrExec $ eff))

getStackEffects' (SuperClassMethodCall className method) = do
    let getEffs :: [(Method, OOMethodSem)] -> [StackEffect]
        getEffs methods = concatMap (\(_, methodSem) -> case methodSem of { InferredByMethod (effs, _) -> effs ; ByDefinition (effs, _) -> effs }) $ filter (\(x,_) -> x == method)  methods
    effs <- lift $ views classInterfaces (getEffs . fromJust . M.lookup className) <$> getState -- :: CheckerM [StackEffect]
    return $ withoutIntersect $ effsAsTuples $ (_Compiled # effs)

getStackEffects' (MethodCall compiledOrExecuted) = do
    let compOrExec = case compiledOrExecuted of { Left _ -> new _Compiled ; Right _ -> new _Executed }
    methodEffs <- lift $ compOrExec . concatMap snd <$> allMethodImplementationss (compiledOrExecuted ^. chosen) -- :: CheckerM (CompiledOrExecuted [StackEffect])
    return $ withoutIntersect $ effsAsTuples methodEffs

getStackEffects' (FieldCall compiledOrExecuted) = do
    let compOrExec = case compiledOrExecuted of { Left _ -> new _Compiled ; Right _ -> new _Executed }
    fieldEffs <- lift $ compOrExec . concatMap snd <$> allFieldImplementations (compiledOrExecuted ^. chosen) -- :: CheckerM (CompiledOrExecuted [StackEffect])
    let fieldEffs' = fieldEffs ^. chosen

    -- iopC "FFFIEELDCALL"
    -- liftIO (mapM_ (putStrLn . render . P.stackEffect) $ fieldEffs' )
    -- iopC $ "is compiled: " ++ (show $ has _Compiled fieldEffs)

    return $ withoutIntersect $ effsAsTuples fieldEffs

getStackEffects' (Class{}) = do

    unlessM (lift $ view allowOOP) $ throwing _OOPNotAllowed ()
    return emptyForthEffect

getStackEffects' (NoNameClash stackCommentEffects clazz method) = do
    iopP "NONAMECLASH"
    let isForced = has (_Just._2.filtered id) stackCommentEffects
    definedEffByClass' <- lift $ getEffOfMethod clazz method
    noDoubleDefinition method definedEffByClass' stackCommentEffects
    effs <- if | isForced -> do
                   let forcedEffs = stackCommentEffects ^?! (_Just._1)
                   lift $ modifyState $ classInterfaces.ix clazz.traverse.filtered (\(method', _) -> method == method')._2 .~ InferredByMethod (forcedEffs, True)

                   return (stackCommentEffects & view (_Just._1))
               | (has (_Just._2.only True) definedEffByClass') -> return (definedEffByClass' & view (_Just._1))
               | otherwise -> throwing (_OOPErrT . _Clash) ("Error in method '" <> method <> "' of class '" <> clazz)

    lift $ modifyState $ set currentCompiling False
    return emptyForthEffect

getStackEffects' (NoName stackCommentEffects exprs clazz method) = do
    iopP "NONAME"
    definedEffByClass' <- lift $ getEffOfMethod clazz method
    let stackCommentEffects'' = (stackCommentEffects `mplus` definedEffByClass')
        stackCommentEffects' = fst <$> stackCommentEffects''
    let isForced = has (_Just._2.filtered id) stackCommentEffects''
        prettyMethod = clazz ++ "." ++ method

    noDoubleDefinition method definedEffByClass' stackCommentEffects

    checkNodes <- view _1

    runMaybeT $ do
      definedEffByClass <- hoistMaybe definedEffByClass'
      definedEffByMethod <- hoistMaybe stackCommentEffects
      lift $ throwing _DefinedTwice ("Effect of method " ++ method ++ " has already been defined in class definition")


    effs <- if | isForced -> do
                   let forcedEffs = stackCommentEffects'' ^?! (_Just._1)
                   lift $ modifyState $ classInterfaces.ix clazz.traverse.filtered (\(method', _) -> method == method')._2 .~ InferredByMethod (forcedEffs, True)

               | otherwise -> (do
                (ForthEffect (compExecEffects, _)) <- withEmpty' $ checkNodes exprs


                let compColonEffects = (compExecEffects ^.. traverse._1)
                    execColonEffects = (compExecEffects ^.. traverse._2)

                forceBeforesEmpty execColonEffects prettyMethod
                forceAftersEmpty execColonEffects prettyMethod

                let checkClassTypeArgument :: StackEffect -> CheckerM StackEffect
                    checkClassTypeArgument eff = do
                      uniqueIdentifier <- identifier <<+= 1
                      let topConsumingType = preview (before._head) eff :: Maybe IndexedStackType
                          classType = (NoReference $ _ClassType # clazz, Just uniqueIdentifier)
                      case topConsumingType of
                       Nothing -> do
                         -- iopC $ "DDDDDDDDDDDd"
                         return $ eff & before %~ (classType :) & after %~ (++ [classType])
                       Just indexedType@(Wildcard, i) -> do
                         -- iopC $ "CCCCCCCCCCC"
                         let replaceWith indexedType target =  target.traverse.filtered (== indexedType) .~ classType
                             replaceStreamTypes indexedType eff = eff
                             -- & streamArgs.traverse._Defining.argType._Right.filtered (== indexedType) .~ classType
                                                                  & streamArgs.traverse._Defining.argType._Just.filtered (== indexedType) .~ classType
                         return $ eff & before %~ tail & before %~ (classType:) & replaceWith  indexedType before
                                      & replaceWith indexedType after & replaceStreamTypes indexedType
                       Just indexedType@(NoReference (ClassType classname), i) -> do

                         iopC "BBBBBBBBBBBBBBBBB"
                         isSubtype <- (_NoReference._ClassType # clazz) `isSubtypeOf` (_NoReference._ClassType # classname)

                         unless isSubtype $ malformedMethodEffect
                         return $ eff & before._head._1._NoReference._ClassType .~ clazz
                       Just _ -> do
                         -- iopC "AAAAAAAAAAAAAAAAAAAAAA"

                         malformedMethodEffect

                    malformedMethodEffect = throwing _TopConsumingMustBeClassType ()


                compColonEffects <- lift $ forM compColonEffects checkClassTypeArgument -- :: CheckerM [StackEffect]
                stackCommentEffects' <- lift $ traverse (mapM checkClassTypeArgument) stackCommentEffects'  -- :: CheckerM (Maybe [StackEffect])


                effs <- lift $ liftM (view chosen) . runExceptT  $ do
                        stEffs <- stackCommentEffects' ?? compColonEffects

                        iopC $ "compcolon EFFEKTE:"
                        mapM_ (iopC . render . P.stackEffect) $ compColonEffects 
                        iop $ "spezifizierte EFFEKTE:"
                        mapM_ (iopC . render . P.stackEffect) $ stEffs 
                        -- iop $ "ZEIGE EFFEKTE:"
                        -- liftIO (mapM_ (putStrLn . render . P.stackEffect) $ compColonEffects )
                        -- liftIO (mapM_ (putStrLn . render . P.stackEffect) $ stEffs )
                        -- let stackCommentIsOK = all (\x -> x `elem` compColonEffects) stEffs
                        -- stackCommentIsOK <- allM (\x -> anyM (\y -> lift $ y `effectIsSubtypeOf` x) compColonEffects) stEffs
                        stackCommentIsOK <- allM (\x -> anyM (\y -> do
                                                 iopC $ "Is " ++ render (P.stackEffect y) ++ " a subtype of " ++ render (P.stackEffect x) ++ "?"
                                                 res <- lift $ y `effectIsSubtypeOf` x
                                                 -- lift $ iop $ "Result is " ++ show res
                                                 return res) compColonEffects) stEffs


                        if stackCommentIsOK then do
                          return stEffs
                        else
                          lift . lift $ throwing (_OOPErrT . _NotMatchingStackComment) prettyMethod

                lift $ modifyState $ classInterfaces.ix clazz.traverse.filtered (\(method', _) -> method == method')._2 .~ InferredByMethod (effs, False))



    lift $ modifyState $ set currentCompiling False

    return emptyForthEffect
