{-# LANGUAGE   FlexibleContexts,  RankNTypes, MultiWayIf, NoMonomorphismRestriction  #-}

module TF.HasEffects.OOP where

import           Control.Error            as E
import           Control.Lens             hiding (noneOf, (??), _Empty)
import           Control.Monad.Error.Lens
import           Control.Monad.Extra
import           Control.Monad.Reader
import           Control.Monad.Writer
import           Text.PrettyPrint         (render)

import           Data.Maybe
import           TF.Util hiding (chosen')
import           TF.SubtypeUtil
-- import qualified TF.DataTypes as DT
-- import           Data.Data
import qualified Data.Map                 as M
import           Text.Parsec              hiding (token)
import qualified TF.Printer               as P
import           TF.Types                 hiding (isSubtypeOf, word)
import TF.Errors

import TF.CheckerUtils
import TF.Type.StackEffect
import TF.Type.Nodes

-- chosen' :: forall b. Lens' (CompiledOrExecuted b) b 
chosen' = compOrExecIso . chosen

compOrExec' cOrE = case cOrE of { Left _ -> Left ; Right _ -> Right }

getStackEffects' (NewObject cOrE) = do
    -- let compOrExec = case cOrE of { Left _ -> new _Compiled ; Right _ -> new _Executed }
    -- let compOrExec = case cOrE of { Left _ -> Left ; Right _ -> Right }
    -- let compOrExec = compOrExec' cOrE
        -- name = case cOrE of { Left x -> x; Right x -> x }
    let name = cOrE ^. chosen'
        -- eff = [StackEffect [] [] [(NoReference $ _ClassType # name, Just 1)]]
        eff = [StackEffect [] [] [IndexedStackType (NoReference $ ClassType name) (Just 1)]]
    -- return $ withoutIntersect (effsAsTuples eff)
    return $ withoutIntersect (effsAsTuples $ cOrE & compOrExecIso.chosen .~ eff)

getStackEffects' (SuperClassMethodCall className method) = do
    let getEffs :: [(Method, OOMethodSem)] -> [StackEffect]
        getEffs methods = concatMap (\(_, methodSem) -> case methodSem of { InferredByMethod (effs, _) -> effs ; ByDefinition (effs, _) -> effs }) $ filter (\(x,_) -> x == method)  methods
    effs <- lift $ views _classInterfaces (getEffs . fromJust . M.lookup className) <$> getState 
    return $ withoutIntersect $ effsAsTuples $ (Compiled effs)

getStackEffects' (MethodCall cOrE) = do
    methodEffs' <- lift $ allMethodImplementationss (cOrE ^. chosen') 
    let methodEffs =  cOrE & chosen' .~ concatMap snd methodEffs'
    return $ withoutIntersect $ effsAsTuples methodEffs

getStackEffects' (FieldCall cOrE) = do
    fieldEffs' <- lift $ allFieldImplementations (cOrE ^. chosen') 
    let fieldEffs = cOrE & chosen' .~ concatMap snd fieldEffs'
    let fieldEffs' = fieldEffs ^. chosen'


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
                   lift $ modifyState $ _classInterfaces.ix clazz.traverse.filtered (\(method', _) -> method == method')._2 .~ InferredByMethod (forcedEffs, True)

                   return (stackCommentEffects & view (_Just._1))
               | (has (_Just._2.only True) definedEffByClass') -> return (definedEffByClass' & view (_Just._1))
               | otherwise -> throwing (_OOPErrT . _Clash) ("Error in method '" <> method <> "' of class '" <> clazz)

    lift $ modifyState $ set _currentCompiling False
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
                   lift $ modifyState $ _classInterfaces.ix clazz.traverse.filtered (\(method', _) -> method == method')._2 .~ InferredByMethod (forcedEffs, True)

               | otherwise -> (do
                (ForthEffect (compExecEffects, _)) <- withEmpty' $ checkNodes exprs


                let compColonEffects = (compExecEffects ^.. traverse._1)
                    execColonEffects = (compExecEffects ^.. traverse._2)

                forceBeforesEmpty execColonEffects prettyMethod
                forceAftersEmpty execColonEffects prettyMethod

                let checkClassTypeArgument :: StackEffect -> CheckerM StackEffect
                    checkClassTypeArgument eff = do
                      uniqueIdentifier <- _identifier <<+= 1
                      let topConsumingType = preview (_before._head) eff :: Maybe IndexedStackType
                          classType = IndexedStackType (NoReference $ ClassType clazz) (Just uniqueIdentifier)
                      case topConsumingType of
                       Nothing -> do
                         return $ eff & _before %~ (classType :) & _after %~ (++ [classType])
                       Just indexedType@(IndexedStackType Wildcard  i) -> do
                         let replaceWith indexedType target =  target.traverse.filtered (== indexedType) .~ classType
                             replaceStreamTypes indexedType eff = eff & _streamArgs.traverse._Defining._argType._Just.filtered (== indexedType) .~ classType
                         return $ eff & _before %~ tail & _before %~ (classType:) & replaceWith  indexedType _before
                                      & replaceWith indexedType _after & replaceStreamTypes indexedType
                       Just indexedType@(IndexedStackType (NoReference (ClassType classname)) i) -> do

                         isSubtype <- (NoReference . ClassType $ clazz) `isSubtypeOf` (NoReference . ClassType $ classname)

                         unless isSubtype $ malformedMethodEffect
                         return $ eff & _before._head._stackType._NoReference._ClassType .~ clazz
                       Just _ -> do

                         malformedMethodEffect

                    malformedMethodEffect = throwing _TopConsumingMustBeClassType ()


                compColonEffects <- lift $ forM compColonEffects checkClassTypeArgument 
                stackCommentEffects' <- lift $ traverse (mapM checkClassTypeArgument) stackCommentEffects'  


                effs <- lift $ liftM (view chosen) . runExceptT  $ do
                        stEffs <- stackCommentEffects' ?? compColonEffects

                        -- iopC $ "compcolon EFFEKTE:"
                        -- mapM_ (iopC . render . P.stackEffect) $ compColonEffects 
                        -- iop $ "spezifizierte EFFEKTE:"
                        -- mapM_ (iopC . render . P.stackEffect) $ stEffs 
                        stackCommentIsOK <- allM (\x -> anyM (\y -> do
                                                 iopC $ "Is " ++ render (P.stackEffect y) ++ " a subtype of " ++ render (P.stackEffect x) ++ "?"
                                                 lift $ y `effectIsSubtypeOf` x
                                                 ) compColonEffects) stEffs


                        if stackCommentIsOK then do
                          return stEffs
                        else
                          lift . lift $ throwing (_OOPErrT . _NotMatchingStackComment) prettyMethod

                lift $ modifyState $ _classInterfaces.ix clazz.traverse.filtered (\(method', _) -> method == method')._2 .~ InferredByMethod (effs, False))



    lift $ modifyState $ set _currentCompiling False

    return emptyForthEffect
