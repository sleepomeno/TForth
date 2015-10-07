{-# LANGUAGE DeriveDataTypeable, DeriveFunctor, FlexibleContexts,
             FlexibleInstances, FunctionalDependencies, LambdaCase, MultiWayIf,
             NoMonomorphismRestriction, OverlappingInstances, OverloadedStrings,
             RankNTypes, RecordWildCards, TemplateHaskell, TupleSections,
             TypeFamilies #-}

module TF.Checker where

import           Control.Arrow
import Control.Applicative
import           Control.Error            as E
import           Control.Lens             hiding (noneOf, (??), _Empty)
import           Control.Monad.Error.Lens
import           Control.Monad.Extra
import           Control.Monad.Reader
import           Control.Monad.Writer
-- import           Lens.Family.Total        hiding ((&))
import           Text.PrettyPrint         (Doc, hcat, nest, render, style, text,
                                           vcat, ($+$), (<+>))
import           TF.StackCalculus
import           TF.WildcardRules

import           Data.List
import           TF.Util
import           Text.Parsec              hiding (token)
import qualified TF.Printer               as P
import           TF.Types                 hiding (isSubtypeOf, word)
import TF.Errors

import TF.CheckerUtils
import TF.HasEffects.HasStackEffects
import TF.HasEffects.Expressions
import TF.HasEffects.ForthWord

checkNodes :: [Node] -> CheckerM ForthEffect
checkNodes nodes = do
  mapM_ collectEffects nodes

  effs <- view effects <$> getState
  return effs

zipzap effects = for effects $ \((oldComp,oldExec),(newComp,newExec)) -> ((oldComp, newComp), (oldExec, newExec))

removeWildcards :: [(StackEffectPair, CompExecEffect)] -> CheckerM [(CompExecEffect, CompExecEffect)]
removeWildcards effs = do
  ( result, stateChanges) <- unzip <$> ( ( mapM ((uncurry oldWildcardDegreeIsGreater
                                                                          >=> uncurry newWildcardDegreeIsGreater
                                                                          >=> uncurry oldTopTypeNotWildcard
                                                                          >=> uncurry newTopTypeNotWildcard
                                                                          >=> uncurry sameDegree)                                                  >>> runWriterT) (zipzap effs) ) :: CheckerM [((StackEffects, StackEffects), [ChangeState])])
  let stateChanges' = filter (not . null) stateChanges
  when (length stateChanges' /= 0 && length (group stateChanges') /= 1) $ do
         lift $ blocked $ mapM_ (iopC . show) stateChanges'
         throwing _DifferentChangeStates ()

  runMaybeT $ do
     stateChanges'' <- hoistMaybe $ headMay stateChanges'
     lift $ blocked $ mapM_ (iopC . show) stateChanges'
     forM_ stateChanges'' $ \case
        ReferenceDegree identifier diff -> lift $ adjustDegree identifier diff
        ResolveUnknown identifier dataType -> lift $ resolveUnknownType identifier dataType





  return $ zipzap $ result
  -- return undefined

resolveUnknownType :: Identifier -> DataType -> CheckerM ()
resolveUnknownType identifier arg = blocked $ do
  iopW $ "RESOLVE UNKNOWN TYPES OF"
  targets1 <- toListOf (definedWords'.traverse._CreateDefinition.traverse.after.traverse.filtered isUnknownType) <$> getState 
  targets2 <- toListOf (definedWords'.traverse._ColonDefinition._2._Checked._1.traverse.streamArgs.traverse._Defining.argType._Just) <$> getState 
  targets3 <- toListOf (definedWords'.traverse._ColonDefinition._2._Checked._1.traverse.after.traverse.filtered isUnknownType) <$> getState 
  iopW . render . vcat . map P.dataType $ targets1 ++ targets2 ++ targets3
  iopW $ "REPLACE WITH: " ++ (render . P.dataType $ (arg, 0))

  modifyState $ definedWords'.traverse._CreateDefinition.traverse.after.traverse.filtered isUnknownType._1 %~ setBaseType arg
  modifyState $ definedWords'.traverse._ColonDefinition._2._Checked._1.traverse.streamArgs.traverse._Defining.filtered hasUnknownArgType.argType %~ over _Just (first $ setBaseType arg)
  modifyState $ definedWords'.traverse._ColonDefinition._2._Checked._1.traverse.before.traverse.filtered isUnknownType._1 %~ setBaseType arg
  modifyState $ classFields %~ imap (updateFields updateStackEffect)
  where
    isUnknownType = isCorrectCreatedWord identifier
    hasUnknownArgType x = has (argType._Just) x && has _UnknownType (baseType' (x ^?! argType._Just._1))
    updateStackEffect :: StackEffect -> StackEffect
    updateStackEffect stEff = stEff & after.traverse.filtered isUnknownType._1 %~ setBaseType arg

updateFields :: (StackEffect -> StackEffect) -> ClassName -> [(Variable, OOFieldSem)] -> [(Variable, OOFieldSem)]
updateFields updateStackEffect _ fields = for fields $ second (fmap updateStackEffect)

adjustDegree identifier diff = do
  blocked $ do
     iopW $ "CHANGE REFERENCE DEGREES BY " ++ show diff ++ " OF"
     targets <- toListOf (definedWords'.traverse._CreateDefinition.traverse.after.traverse.filtered isTarget) <$> getState
     iopW . render . vcat . map P.dataType $ targets
     modifyState $ definedWords'.traverse._CreateDefinition.traverse.after.traverse.filtered isTarget._1 %~ (!! diff) . iterate Reference
  modifyState $ classFields %~ imap (updateFields updateStackEffect)

  -- l4 . modifyState $ definedWords'.traverse._ColonDefinition._2._Checked.traverse.streamArgs.traverse._Defining.filtered hasUnknownArgType.argType %~ over (_Left._Just) ((!! diff) . iterate Reference)
  where
    isUnknownType = isCorrectCreatedWord identifier
    isTarget = isUnknownType
    updateStackEffect stEff = stEff & after.traverse.filtered isTarget._1 %~ (!! diff) . iterate Reference

isCorrectCreatedWord identifier (w, _)  = has _UnknownType (baseType' w)  && ((baseType' w ^?! _UnknownType) == identifier)

applyWildcardRenaming' effs = do
  (result, _) <- unzip <$> mapM (uncurry renameWildcards >>> runWriterT) (zipzap effs)
  return $ zipzap result

collectEffects :: Node -> CheckerM ()
collectEffects a = do

  -- iopC $ "------------"
  -- iopC $ "Apply rules for " ++ (render $ (either P.forthWord P.expr) a)

  tellExpr a

  -- iopC "Next:"
  -- iopC $ render $ P.forthWordOrExpr a
  stE2s <- (`runReaderT` (checkNodes, checkEffects, collectEffects)) $ either getStackEffects getStackEffects a
  let config = defCheckEffectsConfig & forthWordOrExpr .~ Just a & isForcedAssertion .~ (has (_Expr._Assert._2.only True) a)
  flip runReaderT config $ checkEffects stE2s
  -- iopC $ show stE2s

  

checkEffects :: ForthEffect -> ReaderT CheckEffectsConfig CheckerM ()
checkEffects (ForthEffect (stE2s, IntersectionType newCompileI newExecI)) = do

  s <- lift getState
  let (ForthEffect (realEffs, IntersectionType oldCompileI oldExecI)) = s ^. effects

  let effs' = zipzap $ liftM2 (,) realEffs stE2s

  effs <- lift $ applyWildcardRenaming' effs'

  let reduce effs = do
        -- iopC "effsWithoutTopWildcardBefore"
        -- liftIO . mapM (putStrLn . (\(c,e) -> render $ P.stackEffect c $+$ P.stackEffect e) . fst) $ effs
        -- showEffs effs
        effsWithoutTopWildcard <- removeWildcards effs
        -- iopC "after removeWildcards"
        -- iopC "effsWithoutTopWildcardAfter"
        -- liftIO . mapM (putStrLn . (\(c,e) -> render $ P.stackEffect c $+$ P.stackEffect e) . fst) $ effsWithoutTopWildcard
        reducedEffects <- mapM (\(comp,exec) -> do
                                   comp' <- uncurry applyRule4 comp
                                   exec' <- uncurry applyRule4 exec
                                   return (comp', exec')) effsWithoutTopWildcard :: CheckerM [(StackEffects, StackEffects)]
        
        if effs == reducedEffects then
           return reducedEffects
        else
           reduce reducedEffects

  -- iopC "before deduce"
  reducedEffects <- lift (reduce effs) :: ReaderT CheckEffectsConfig CheckerM [(StackEffects, StackEffects)]
  -- iopC "after deduce"

  -- exportWords $ reducedEffects ^.. (traverse.both._2)
  reducedEffects' <- lift (exportWords' reducedEffects)  -- ^.. (traverse.both._2)

  let resultingEffects' :: [StackRuleM (StackEffect, StackEffect)]
      resultingEffects' = map (\(comp, exec) -> do
                                  comp' <- local (set checkState COMPILESTATE) $ uncurry applyRules comp
                                  exec' <- local (set checkState INTERPRETSTATE) $ uncurry applyRules exec
                                  return (comp', exec')) reducedEffects'
                                  -- return (comp', exec')) reducedEffects

  composedEffects <- mapM runExceptT resultingEffects'
  let effectsWithClash = toListOf (traverse._Left) . filter isLeft $ composedEffects
      compileEffectClash = COMPILESTATE `elem` effectsWithClash
      execEffectClash = INTERPRETSTATE `elem` effectsWithClash

  forbidMultiEffs <- lift $ views allowMultipleEffects not

  let (nrOfOldCompEffs, nrOfOldExecEffs) = unzip realEffs & both %~ length . nub
      (nrOfNewCompEffs, nrOfNewExecEffs) = unzip stE2s    & both %~ length . nub

  -- let compileEffectError = compileEffectClash && not (oldCompileI || newCompileI)
  --     execEffectError = execEffectClash && not (oldExecI || newExecI)
  let compileEffectError = compileEffectClash && (((nrOfOldCompEffs > 1 && not oldCompileI) ||
                                                  (nrOfNewCompEffs > 1 && not newCompileI)) || not (oldCompileI || newCompileI))
      execEffectError = execEffectClash && (((nrOfOldExecEffs > 1 && not oldExecI) ||
                                                  (nrOfNewExecEffs > 1 && not newExecI)) || not (oldExecI || newExecI))

  let errorInfo = do
        lift . lift . lift $ tell $ Info [] [CheckFailure realEffs stE2s] []
        fwordOrExpr <- view forthWordOrExpr
        when (has (_Just._Expr._Assert) fwordOrExpr) $
           lift . lift . lift $ tell $ Info [] [] [AssertFailure realEffs stE2s] 

        return $ case fwordOrExpr of
          Just x  -> render $ either P.infoForthWord P.infoExpr x
          Nothing -> ""



  when ((compileEffectError || execEffectError)) $ do
    iop $ "compileEffectError: " <> show compileEffectError
    iop $ "execEffectERror: " <> show execEffectError
    iop $ "oldCompileI: " <> show oldCompileI
    iop $ "newCompileI: " <> show newCompileI
    iop $ "oldExecI: " <> show oldExecI
    iop $ "newExecI: " <> show newExecI
    message <- errorInfo
    throwing (_TypeClashM._MultiEffs) message

  validEffects <- fmap (toListOf (traverse._Right) . filter isRight) . mapM runExceptT $ resultingEffects'

  let typeChecks = (not . null $ validEffects)

  -- iopC $ "Apply rules for " ++ (render $ (either P.forthWord P.expr) a)

  -- lift $ guard typeChecks

  unless typeChecks $ do
    message <- errorInfo
    throwing _Clash message

  -- lift $ modifyState $ set effects validEffects
  lift $ modifyState $ effects._Wrapped._1 .~ validEffects

  updateIntersectionType nrOfOldCompEffs nrOfNewCompEffs compileEffect oldCompileI newCompileI
  updateIntersectionType nrOfOldExecEffs nrOfNewExecEffs execEffect oldExecI newExecI

  return ()

-- moeglicherweise die compexeceffect-pairs wieder unzippen, um zu
-- schauen, ob es unterschiedliche exec- oder comp-effekte oder beide gegeben hat

updateIntersectionType nrOfOldEffs nrOfNewEffs effLens oldI newI = 
  if | (nrOfOldEffs > 1 && nrOfNewEffs > 1) ->
          lift $ modifyState $ effects._Wrapped._2.effLens .~ (oldI && newI)
     | (nrOfOldEffs > 1 && nrOfNewEffs <= 1) -> 
          lift $ modifyState $ effects._Wrapped._2.effLens .~ oldI
     | (nrOfOldEffs <= 1 && nrOfNewEffs > 1) -> 
          lift $ modifyState $ effects._Wrapped._2.effLens .~ newI
     | (nrOfOldEffs == 1 && nrOfNewEffs == 1) -> 
          return ()
    

exportWords' :: [(StackEffects, StackEffects)] -> CheckerM [(StackEffects, StackEffects)]
exportWords' effs = do
  let effs' = map (\(x,y) -> (snd x, snd y)) effs
  effs'' <- forM effs' $ \(comp, exec) -> do
                comp' <- st comp
                exec' <- st exec
                return (comp', exec')
  return $ zipWith (\((x,x'),(y,y')) (c,e) -> ((x,c),(y,e))) effs effs''

st :: StackEffect -> CheckerM StackEffect
st (StackEffect b args a) = do
  args' <- mapM handleArgs args
  return $ StackEffect b args' a

handleArgs :: DefiningOrNot -> CheckerM DefiningOrNot
handleArgs d@(Right _) = return d
handleArgs (Left arg) = do
    let currentType = view argType arg :: (Maybe IndexedStackType)

    let typeOfArg = maybe (Left $ (Wildcard, Just 0)) Right currentType :: Either IndexedStackType IndexedStackType
    uniqueId <- identifier <<+= 1
    uniqueId2 <- identifier <<+= 1
    uniqueId3 <- identifier <<+= 1
    uniqueId4 <- identifier <<+= 1
    -- let maybeRuntimeType = _Just.chosen.traverse.both %~ toStackEffect $ view runtimeEffect arg :: Maybe (Either [(StackEffect,StackEffect)] [(StackEffect,StackEffect)])
    let maybeRuntimeType = _Just.traverse.both %~ toStackEffect $ view runtimeEffect arg :: Maybe [(StackEffect,StackEffect)]
        initialRuntimeType = StackEffect [] [] [first Reference $ fromMaybe (Wildcard, Just 0) currentType]
        defaultRuntimeType = StackEffect [] [] [first Reference defaultR]
        defaultR = case currentType of
          Nothing -> (UnknownType uniqueId, Just uniqueId2)
          Just (t, i) -> if baseType' t == Wildcard then
                           (setBaseType (UnknownType uniqueId) t, Just uniqueId2)
                         else
                           (t, i)
          -- Just x -> x
        defaultRuntimeType' = StackEffect [] [] [first Reference defaultR']
        defaultR' = case currentType of
          -- Nothing -> (UnknownType uniqueId, Just uniqueId2)
          Nothing -> (WildcardWrapper, Just uniqueId3)
          Just x -> x

    (runtimeType) <- if isJust maybeRuntimeType then
                     -- if isJust (view resolved arg) then
                               -- TODO remove _runtimeprocessed 
                                -- if (has (_Just._RuntimeProcessed) maybeRuntimeType) then
                                -- -- if (view runtimeChecked arg) then
                                --   undefined >>
                                --   return ((toListOf (_Just.chosen.traverse._1) maybeRuntimeType), True)
                                (withEmpty $ do

                                  iop $ "defaulruntime is"
                                  iop $ show defaultRuntimeType
                                  modifyState $ effects._Wrapped._1.traverse._1 .~ defaultRuntimeType'
                                  -- iopC "Current Effects"

                                  -- effs <- view realEffects <$> getState
                                  -- liftIO . mapM (putStrLn . (\(c,e) -> render $ P.stackEffect c $+$ P.stackEffect e)) $ effs
                                  -- iopC "SSSSSSSSSSSSSSS"
                                  let runtimeEffects' = withoutIntersect $ (maybeRuntimeType ^?! _Just)

                                  -- iopC "runtime effects"
                                  -- liftIO . mapM (putStrLn . (\(c,e) -> render $ P.stackEffect c $+$ P.stackEffect e)) $ runtimeEffects'
                                  iop "BEFORE"
                                  flip runReaderT defCheckEffectsConfig $ checkEffects runtimeEffects'
                                  iop "AFTER"
                                  result <- toListOf (effects._Wrapped._1.traverse._1) <$> getState

                                  result' <- replaceWrappers result
                                  

                                  iopC "result of runtime checking"
                                  mapM_ (iopC . (render . P.stackEffect)) $ result'

                                  return result')

                            else
                                return [defaultRuntimeType]

    when (has (resolved._Just) arg) $
      modifyState $ definedWords'.(at (arg ^?! resolved._Just)) ?~ (new _CreateDefinition runtimeType)
    -- let arg' =  arg & argType .~ (either (const Nothing) Just typeOfArg) & runtimeChecked .~ checked
    let arg' =  arg & argType .~ (either (const Nothing) Just typeOfArg) 
    return $ Left $ arg'


