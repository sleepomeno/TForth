{-# LANGUAGE NoMonomorphismRestriction,FlexibleContexts,RankNTypes, LambdaCase, MultiWayIf  #-}

module TF.Checker (
  checkNodes
  ) where

import Prelude hiding (last)
import           Control.Arrow
import           Control.Error            as E
-- import           Control.Lens             hiding (noneOf, (??), _Empty)
import Control.Lens (filtered,has,(^?!),only,(<<+=),imap,_Wrapped)
import Lens.Simple
import           Control.Monad.Error.Lens
import           Control.Monad.Extra
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Writer
-- import           Lens.Family.Total        hiding ((&))
import           Text.PrettyPrint         (render, vcat)
import           TF.StackCalculus
import           TF.WildcardRules
import Data.Maybe (fromJust)

import           Data.List hiding (insert,last)
import           TF.Util
import           Text.Parsec              hiding (token)
import qualified TF.Printer               as P
import           TF.Types                 hiding (isSubtypeOf, word)
import TF.HandleDegrees
import TF.Errors
import Data.Tree
import Data.Tree.Zipper hiding (after,before,first,label)

import TF.CheckerUtils
import TF.HasEffects.HasStackEffects
import TF.HasEffects.Expressions()
import TF.Type.StackEffect
import TF.Type.Nodes

checkNodes :: [Node] -> CheckerM ForthEffect
checkNodes nodes = do
  mapM_ collectEffects nodes

  view _effects <$> getState

zipzap effects = for effects $ \((oldComp,oldExec),(newComp,newExec)) -> ((oldComp, newComp), (oldExec, newExec))

removeWildcards :: [(StackEffectPair, CompExecEffect)] -> CheckerM [(CompExecEffect, CompExecEffect)]
removeWildcards effs = do
  ( result, stateChanges) <- unzip <$> ( ( mapM ((uncurry oldWildcardDegreeIsGreater
                                                  >=> uncurry newWildcardDegreeIsGreater
                                                  >=> uncurry oldTopTypeNotWildcard
                                                  >=> uncurry newTopTypeNotWildcard
                                                  >=> uncurry sameDegree)                                                  >>> runWriterT) (zipzap effs) ) :: CheckerM [((StackEffects, StackEffects), [ChangeState])])
  let stateChanges' = filter (not . null) stateChanges
  when (not (null stateChanges') && length (group stateChanges') /= 1) $ do
         lift $ blocked iopC $ mapM_ (iopC . show) stateChanges'
         throwing _DifferentChangeStates ()

  runMaybeT $ do
     stateChanges'' <- hoistMaybe $ headMay stateChanges'
     lift $ blocked iopC $ mapM_ (iopC . show) stateChanges'
     forM_ stateChanges'' $ \case
        ReferenceDegree identifier diff -> lift $ adjustDegree identifier diff
        ResolveUnknown identifier dataType -> lift $ resolveUnknownType identifier dataType





  return $ zipzap result

resolveUnknownType :: Identifier -> DataType -> CheckerM ()
resolveUnknownType identifier arg = blocked iopC $ do
  -- iopW "RESOLVE UNKNOWN TYPES OF"
  targets1 <- toListOf (_definedWords'.traverse._CreateDef.traverse._after.traverse.filtered isUnknownType) <$> getState 
  targets2 <- toListOf (_definedWords'.traverse._ColDef.processedEffects._Checked._stefwiMultiEffects._Wrapped.traverse._streamArgs.traverse._Defining._argType._Just) <$> getState 
  targets3 <- toListOf (_definedWords'.traverse._ColDef.processedEffects._Checked._stefwiMultiEffects._Wrapped.traverse._after.traverse.filtered isUnknownType) <$> getState 
  iopW . render . vcat . map P.dataType $ targets1 ++ targets2 ++ targets3
  -- iopW $ "REPLACE WITH: " ++ (render . P.dataType $ (arg, 0))

  modifyState $ _definedWords'.traverse._CreateDef.traverse._after.traverse.filtered isUnknownType._stackType %~ setBaseType arg
  modifyState $ _definedWords'.traverse._ColDef.processedEffects._Checked._stefwiMultiEffects._Wrapped.traverse._streamArgs.traverse._Defining.filtered hasUnknownArgType._argType %~ over _Just (over _stackType $ setBaseType arg)
  modifyState $ _definedWords'.traverse._ColDef.processedEffects._Checked._stefwiMultiEffects._Wrapped.traverse._before.traverse.filtered isUnknownType._stackType %~ setBaseType arg
  modifyState $ _classFields %~ imap (updateFields updateStackEffect)
  where
    isUnknownType = isCorrectCreatedWord identifier
    hasUnknownArgType x = has (_argType._Just) x && has _UnknownType (baseType (x ^?! _argType._Just._stackType))
    updateStackEffect :: StackEffect -> StackEffect
    updateStackEffect stEff = stEff & _after.traverse.filtered isUnknownType._stackType %~ setBaseType arg

updateFields :: (StackEffect -> StackEffect) -> ClassName -> [(Variable, OOFieldSem)] -> [(Variable, OOFieldSem)]
updateFields updateStackEffect _ fields = for fields $ second (fmap updateStackEffect)

adjustDegree identifier diff = do
  blocked iopC $ do
     iopW $ "CHANGE REFERENCE DEGREES BY " ++ show diff ++ " OF"
     targets <- toListOf (_definedWords'.traverse._CreateDef.traverse._after.traverse.filtered isTarget) <$> getState
     iopW . render . vcat . map P.dataType $ targets
     modifyState $ _definedWords'.traverse._CreateDef.traverse._after.traverse.filtered isTarget._stackType %~ (!! diff) . iterate Reference
  modifyState $ _classFields %~ imap (updateFields updateStackEffect)

  -- l4 . modifyState $ _definedWords'.traverse._ColDef.processedEffects._Checked.traverse._streamArgs.traverse._Defining.filtered hasUnknownArgType._argType %~ over (_Left._Just) ((!! diff) . iterate Reference)
  where
    isUnknownType = isCorrectCreatedWord identifier
    isTarget = isUnknownType
    updateStackEffect stEff = stEff & _after.traverse.filtered isTarget._stackType %~ (!! diff) . iterate Reference

isCorrectCreatedWord identifier (IndexedStackType w  _)  = has _UnknownType (baseType w)  && ((baseType w ^?! _UnknownType) == identifier)

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
  stE2s <- (`runReaderT` (checkNodes, checkEffects, collectEffects)) $ either getStackEffects getStackEffects $ view nodeIso a
  let config = def & forthWordOrExpr .~ Just a & isForcedAssertion .~ has (_Expr._Assert._2.only True) a
  flip runReaderT config $ checkEffects stE2s
  -- iopC $ show stE2s

  

checkEffects :: ForthEffect -> ReaderT CheckEffectsConfig CheckerM ()
checkEffects (ForthEffect (stE2s, Intersections newCompileI newExecI)) = do

  s <- lift getState
  let (ForthEffect (realEffs, Intersections oldCompileI oldExecI)) = s ^. _effects

  let effs' = zipzap $ liftM2 (,) realEffs stE2s

  effs <- lift $ applyWildcardRenaming' effs'

  let reduce effs = do
        effsWithoutTopWildcard <- removeWildcards effs
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

  reducedEffects' <- lift (exportWords' reducedEffects)  

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

  -- forbidMultiEffs <- lift $ views allowMultipleEffects not

  let (nrOfOldCompEffs, nrOfOldExecEffs) = unzip realEffs & both %~ length . nub
      (nrOfNewCompEffs, nrOfNewExecEffs) = unzip stE2s    & both %~ length . nub

  -- let compileEffectError = compileEffectClash && not (oldCompileI || newCompileI)
  --     execEffectError = execEffectClash && not (oldExecI || newExecI)
  let compileEffectError = compileEffectClash && (((nrOfOldCompEffs > 1 && not oldCompileI) ||
                                                  (nrOfNewCompEffs > 1 && not newCompileI)) || not (oldCompileI || newCompileI))
      execEffectError = execEffectClash && (((nrOfOldExecEffs > 1 && not oldExecI) ||
                                                  (nrOfNewExecEffs > 1 && not newExecI)) || not (oldExecI || newExecI))

  let errorInfo = do
        fwordOrExpr <- asks (view forthWordOrExpr)
        tellErrors' <- asks (view tellErrors)
        lift . lift . lift $ when tellErrors' $
           if (has (_Just._Expr._Assert) fwordOrExpr) then
              tell $ Info [] [AssertFailure realEffs stE2s]
           else
              tell $ Info [CheckFailure realEffs stE2s] []

        return $ case fwordOrExpr of
          Just x  -> render $ either P.infoForthWord P.infoExpr $ view nodeIso $ x
          Nothing -> ""



  when (compileEffectError || execEffectError) $ do
    iopC $ "compileEffectError: " <> show compileEffectError
    iopC $ "execEffectERror: " <> show execEffectError
    iopC $ "execEffectClash: " <> show execEffectClash
    iopC $ "oldCompileI: " <> show oldCompileI
    iopC $ "newCompileI: " <> show newCompileI
    iopC $ "oldExecI: " <> show oldExecI
    iopC $ "newExecI: " <> show newExecI
    message <- errorInfo
    iopC $ "message: " <> show message
    -- throwing (_TypeClashM._MultiEffs) message
    throwing _Clash message

  validEffects <- fmap (toListOf (traverse._Right) . filter isRight) . mapM runExceptT $ resultingEffects'

  let typeChecks = (not . null $ validEffects)


  unless typeChecks $ do
    message <- errorInfo
    throwing _Clash message

  lift $ modifyState $ _effects._Wrapped._1 .~ validEffects

  updateIntersectionType nrOfOldCompEffs nrOfNewCompEffs _compileEffect oldCompileI newCompileI
  updateIntersectionType nrOfOldExecEffs nrOfNewExecEffs _execEffect oldExecI newExecI

  return ()

-- moeglicherweise die compexeceffect-pairs wieder unzippen, um zu
-- schauen, ob es unterschiedliche exec- oder comp-effekte oder beide gegeben hat

updateIntersectionType :: Int -> Int -> (Lens' Intersections Bool) -> Bool -> Bool -> ReaderT CheckEffectsConfig CheckerM ()
updateIntersectionType nrOfOldEffs nrOfNewEffs effLens oldI newI = 
  if | (nrOfOldEffs > 1 && nrOfNewEffs > 1) ->
          lift $ modifyState $ _effects._Wrapped._2.effLens .~ (oldI && newI)
     | (nrOfOldEffs > 1 && nrOfNewEffs <= 1) -> 
          lift $ modifyState $ _effects._Wrapped._2.effLens .~ oldI
     | (nrOfOldEffs <= 1 && nrOfNewEffs > 1) -> 
          lift $ modifyState $ _effects._Wrapped._2.effLens .~ newI
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
handleArgs d@(NotDefining _) = return d
handleArgs (Defining arg) = do
    let currentType = view _argType arg :: (Maybe IndexedStackType)

    let typeOfArg = maybe (Left $ IndexedStackType Wildcard  (Just 0)) Right currentType :: Either IndexedStackType IndexedStackType
    uniqueId <- _identifier <<+= 1
    uniqueId2 <- _identifier <<+= 1
    uniqueId3 <- _identifier <<+= 1
    -- let maybeRuntimeType = _Just.chosen.traverse.both %~ toStackEffect $ view runtimeEffect arg :: Maybe (Either [(StackEffect,StackEffect)] [(StackEffect,StackEffect)])
    -- let maybeRuntimeType = _Just.traverse.both %~ toStackEffect $ view runtimeEffect arg :: Maybe [(StackEffect,StackEffect)]
    let maybeRuntimeType = view _runtimeEffect arg :: Maybe ForthEffect -- [(StackEffect,StackEffect)]

        -- initialRuntimeType = StackEffect [] [] [over _stackType Reference $ fromMaybe (IndexedStackType Wildcard  (Just 0)) currentType]

        defaultRuntimeType = StackEffect [] [] [defaultR & _stackType %~ Reference]

        defaultR = case currentType of
          Nothing -> IndexedStackType (UnknownType uniqueId) (Just uniqueId2)
          Just (IndexedStackType t  i) -> if baseType t == Wildcard then
                           IndexedStackType (setBaseType (UnknownType uniqueId) t) (Just uniqueId2)
                         else
                           (IndexedStackType t i)
          -- Just x -> x
        defaultRuntimeType' = StackEffect [] [] [defaultR' & _stackType %~ Reference]

        defaultR' = case currentType of
          -- Nothing -> (UnknownType uniqueId, Just uniqueId2)
          Nothing -> IndexedStackType WildcardWrapper ( Just uniqueId3)
          Just x -> x

    (runtimeType) <- if isJust maybeRuntimeType then
                                (withEmpty $ do

                                  -- undefined
                                  iopC $ "defaulruntime is"
                                  iopC $ show defaultRuntimeType
                                  modifyState $ _effects._Wrapped._1.traverse._1 .~ defaultRuntimeType'
                                  let runtimeEffects'' = maybeRuntimeType ^?! _Just
                                      runtimeEffects' = runtimeEffects'' 

                                  iopC "BEFORE checking runtime effect of defining argument"
                                  flip runReaderT def $ checkEffects runtimeEffects'
                                  iopC "AFTER checking runtime effect of defining argument"
                                  result <- toListOf (_effects._Wrapped._1.traverse._1) <$> getState

                                  result' <- replaceWrappers result
                                  

                                  iopC "result of runtime checking of defining argument"
                                  mapM_ (iopC . (render . P.stackEffect)) $ result'

                                  return result')

                            else
                                return [defaultRuntimeType]

    when (has (_definingArgInfo._resolved._Just) arg) $
      modifyState $ (_definedWords'.(at (arg ^?! _definingArgInfo._resolved._Just))) ?~ CreateDef runtimeType
    -- let arg' =  arg & _argType .~ (either (const Nothing) Just typeOfArg) & runtimeChecked .~ checked
    let arg' =  arg & _argType .~ either (const Nothing) Just typeOfArg
    return $ Defining $ arg'



tellExpr :: Node -> CheckerM ()
tellExpr expr = do
  -- lift . lift $ tell (Info [expr] [] [])

  let modState f = modify $ _checkedExpressions %~ f
  modState $ insert (Node "" []) . last . children
  modState $ modifyTree (\t -> t { rootLabel = render $ P.infoNode expr })
  modState $ \s ->
    if isContained s then
      fromJust $ parent s
    else
      s
