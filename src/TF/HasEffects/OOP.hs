{-# LANGUAGE   FlexibleContexts,  MultiWayIf  #-}

module TF.HasEffects.OOP where

import           Control.Error            as E
import           Control.Lens             hiding (noneOf, (??), _Empty)
import           Control.Monad.Error.Lens
import           Control.Monad.Extra
import           Control.Monad.Reader
import           Control.Monad.Writer
import           Text.PrettyPrint         (render)

import           Data.Maybe
import           TF.Util
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

compOrExec' cOrE = case cOrE of { Left _ -> Left ; Right _ -> Right }

getStackEffects' (NewObject cOrE) = do
    -- let compOrExec = case cOrE of { Left _ -> new _Compiled ; Right _ -> new _Executed }
    -- let compOrExec = case cOrE of { Left _ -> Left ; Right _ -> Right }
    let compOrExec = compOrExec' cOrE
        name = case cOrE of { Left x -> x; Right x -> x }
        -- eff = [StackEffect [] [] [(NoReference $ _ClassType # name, Just 1)]]
        eff = [StackEffect [] [] [(NoReference $ ClassType name, Just 1)]]
    return $ withoutIntersect (effsAsTuples $ compOrExec eff)

getStackEffects' (SuperClassMethodCall className method) = do
    let getEffs :: [(Method, OOMethodSem)] -> [StackEffect]
        getEffs methods = concatMap (\(_, methodSem) -> case methodSem of { InferredByMethod (effs, _) -> effs ; ByDefinition (effs, _) -> effs }) $ filter (\(x,_) -> x == method)  methods
    effs <- lift $ views classInterfaces (getEffs . fromJust . M.lookup className) <$> getState -- :: CheckerM [StackEffect]
    return $ withoutIntersect $ effsAsTuples $ (Left effs)

getStackEffects' (MethodCall cOrE) = do
    let compOrExec = compOrExec' cOrE
    methodEffs <- lift $ compOrExec . concatMap snd <$> allMethodImplementationss (cOrE ^. chosen) -- :: CheckerM (CompiledOrExecuted [StackEffect])
    return $ withoutIntersect $ effsAsTuples methodEffs

getStackEffects' (FieldCall cOrE) = do
    let compOrExec = compOrExec' cOrE
    fieldEffs <- lift $ compOrExec . concatMap snd <$> allFieldImplementations (cOrE ^. chosen) -- :: CheckerM (CompiledOrExecuted [StackEffect])
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
                      let topConsumingType = preview (_before._head) eff :: Maybe IndexedStackType
                          classType = (NoReference $ ClassType clazz, Just uniqueIdentifier)
                      case topConsumingType of
                       Nothing -> do
                         -- iopC $ "DDDDDDDDDDDd"
                         return $ eff & _before %~ (classType :) & _after %~ (++ [classType])
                       Just indexedType@(Wildcard, i) -> do
                         -- iopC $ "CCCCCCCCCCC"
                         let replaceWith indexedType target =  target.traverse.filtered (== indexedType) .~ classType
                             replaceStreamTypes indexedType eff = eff
                             -- & streamArgs.traverse._Defining.argType._Right.filtered (== indexedType) .~ classType
                                                                  & _streamArgs.traverse._Defining._argType._Just.filtered (== indexedType) .~ classType
                         return $ eff & _before %~ tail & _before %~ (classType:) & replaceWith  indexedType _before
                                      & replaceWith indexedType _after & replaceStreamTypes indexedType
                       Just indexedType@(NoReference (ClassType classname), i) -> do

                         iopC "BBBBBBBBBBBBBBBBB"
                         isSubtype <- (NoReference . ClassType $ clazz) `isSubtypeOf` (NoReference . ClassType $ classname)

                         unless isSubtype $ malformedMethodEffect
                         return $ eff & _before._head._1._NoReference._ClassType .~ clazz
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
                                                 lift $ y `effectIsSubtypeOf` x
                                                 -- lift $ iop $ "Result is " ++ show res
                                                 ) compColonEffects) stEffs


                        if stackCommentIsOK then do
                          return stEffs
                        else
                          lift . lift $ throwing (_OOPErrT . _NotMatchingStackComment) prettyMethod

                lift $ modifyState $ classInterfaces.ix clazz.traverse.filtered (\(method', _) -> method == method')._2 .~ InferredByMethod (effs, False))



    lift $ modifyState $ set currentCompiling False

    return emptyForthEffect
