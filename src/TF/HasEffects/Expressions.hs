{-# LANGUAGE FlexibleContexts, NoMonomorphismRestriction, LambdaCase  #-}

module TF.HasEffects.Expressions (getStackEffects) where

import           Control.Error            as E
import           Control.Lens             hiding (noneOf, (??), _Empty)
import Data.Monoid (getAny)
import           Control.Monad.Error.Lens
import           Control.Monad.Extra
import           Control.Monad.Reader
import           Control.Monad.Cont
import           Text.PrettyPrint         (render)
import Data.Function (on)

import           Data.List
import           TF.Util hiding (chosen')
-- import qualified TF.DataTypes as DT
-- import           Data.Data
import           Text.Parsec              hiding (token)
import qualified TF.Printer               as P
import           TF.Types                 hiding (isSubtypeOf, word)
import TF.Errors

import TF.CheckerUtils
import TF.HasEffects.HasStackEffects
import qualified TF.HasEffects.ControlStructures as CS
import qualified TF.HasEffects.OOP as OOP
import TF.HasEffects.ForthWord()
import TF.Type.StackEffect
import TF.Type.Nodes

chosen' = compOrExecIso . chosen

instance HasStackEffects Expr where

  getStackEffects (ControlExpr x) = CS.getStackEffects' x

  getStackEffects (OOPExpr x) = OOP.getStackEffects' x

  getStackEffects (Postpone _) = return emptyForthEffect

  getStackEffects (PostponeImmediate w) = do
    getStackEffects w

  getStackEffects (Interpreted forthWordsOrExprs) = do
    lift $ modifyState $ set _currentCompiling False
    checkNodes <- view _1
    compExecEffs <- withEmpty' $ checkNodes forthWordsOrExprs
    lift $ modifyState $ set _currentCompiling True
    return compExecEffs

  getStackEffects (Create create init does) = do
    uniqueId <- _identifier <<+= 1


    checkNodes <- view _1
    let go :: (Node, [Node], Maybe Node, Maybe [Node]) -> CheckerM ForthEffect
        go (create, exprs, comma, does) = withEmpty $ do
          checkNodes (create : exprs)

          runMaybeT $ do
            c <- hoistMaybe comma
            lift $ checkNodes [c]
          result <- view _effects <$> getState

          maybeDoes <- runMaybeT $ do
            exprs' <- hoistMaybe does
            forthEff <- lift $ withEmpty $ checkNodes exprs'
            return $ forthEff 

          result' <- case maybeDoes of
                        Nothing -> return result
                        Just doesEffects -> do
                          let newCreating = create & elementOf (_ForthWord.l.traverse._streamArgs.traverse._Defining) 0._runtimeEffect ?~ doesEffects
                          -- TODO make sure compiletime before and after are empty
                          go (newCreating, exprs, comma, Nothing)



          return result'
  
    withEmpty' $ do
      cr <- checkNodes [create]

      maybeInitType <- runMaybeT $ (do
        (exprs, comma) <- hoistMaybe init
        lift $ checkNodes exprs
        stEffs <- lift $ effectsOfState
        let typeOfCreated :: Maybe IndexedStackType
            typeOfCreated = stEffs ^?! _head & preview (_after._head)

        -- when (typeOfCreated == Nothing) $ iop "UNGLEICH NOTHING"

        lift $ checkNodes [comma]


        effs <- lift effectsOfState
        -- iopC "Current State:\n"
        -- liftIO $ mapM_ (putStrLn . render . P.stackEffect) effs
        maybe (liftUp . lift  $ preview (_head._before._head) effs E.?? (_Impossible # "No top stack value in maybeInitType")) return typeOfCreated) :: CheckerM (Maybe IndexedStackType)

      result <- case maybeInitType of
                    Nothing -> go (create, [], Nothing, does)
                    Just initType -> do
                      let newCreating = create & elementOf (_ForthWord.l.traverse._streamArgs.traverse._Defining) 0._argType ?~ initType
                      go (newCreating, init ^?! _Just._1, init ^? _Just._2, does)

      effs <- effectsOfState
      -- iopC "Show effects of create:\n"
      -- showEffs' effs
      return result

    where
       l = if has (_ForthWord._DefE) create then
             _DefE.chosen'._2._stefwiMultiEffects._Wrapped
           else
             _KnownWord._stacksEffects.chosen''._Wrapped

    -- iopC "Show effects of create:\n"
    -- liftIO $ mapM_ (putStrLn . render . P.stackEffect) effs

    -- iopC $ "The Create-----\n"
    -- iopC $ render . either P.forthWord P.expr $ create

  getStackEffects (ColonExprImmediate colonName stackCommentEffects bodyWords) = getStackEffects (ColonExpr colonName stackCommentEffects bodyWords)


  getStackEffects (Tick effects pw) = do
    unless (length effects == 1) $ throwing (_ErrorTick . _MultipleEffects) () 
    let effect = effects ^?! _head
    when (has (_before._head) effect) $ throwing (_ErrorTick . _MalformedAssert) "No before allowed!"
    when (has (_after._head) effect) $ throwing (_ErrorTick . _MalformedAssert) "No After allowed!"
    let args = toListOf (_streamArgs.traverse._NotDefining._runtimeSpecified._Just._KnownR) effect
    unless (1 == length args) $ throwing (_ErrorTick . _MalformedAssert) "Exactly one knownR stream argument necessary!"

    let runtimeEff'' = args ^?! _head -- .stackEffectIso

    let pw' = pw & _stacksEffects._CompiledEff._Wrapped.traverse._streamArgs.traverse._NotDefining._runtimeSpecified._Just %~ setEffect
        setEffect :: RuntimeSpecification -> RuntimeSpecification
        setEffect = \case
          UnknownR i -> ResolvedR i runtimeEff''-- (effect ^. from stackEffectIso)
          x          -> x
    let resolvedRuntimes = pw' ^.. _stacksEffects._CompiledEff._Wrapped.traverse._streamArgs.traverse._NotDefining._runtimeSpecified._Just._ResolvedR :: [(UniqueArg, StackEffect)]
        pw'' = pw' & _stacksEffects._CompiledEff._Wrapped.traverse %~ ((_before.traverse %~ resolveRuntimeType resolvedRuntimes) . (_after.traverse %~ resolveRuntimeType resolvedRuntimes))

    getStackEffects (KnownWord pw'')

  getStackEffects (Execute effects') = do
    iop "getStackEffects Execute"
    let effects = effects' ^. chosen'
    unless (length effects == 1) $ throwing (_ErrorE . _MultipleEffects) () 
    let effect = effects ^?! _head
    when (has (_before._head) effect) $ throwing (_ErrorE . _MalformedAssert) "No before allowed!"
    unless (1 == length (view _after effect)) $ throwing (_ErrorE . _MalformedAssert) "Exactly One After data type!"
    let xts = toListOf (_after.traverse._stackType._NoReference._ExecutionType._exectokenRuntimeSpecified._Just._KnownR) effect
    unless (1 == length xts) $ throwing (_ErrorE . _MalformedAssert) "Exactly one xt data type!"

    let eff = xts ^?! _head

    let compOrExec = if has _Compiled effects' then Left else Right

    collectEffects <- view _3
    lift $ collectEffects (Expr $ Assert effects' False) -- TODO take forced from parsed assertion

    uniqueIdentifier <- lift $ _identifier <<+= 1
    -- let executeEffs = effsAsTuples $ compOrExec [eff & _before %~ ((Wildcard, Just uniqueIdentifier):)] 
    let executeEffs = effsAsTuples $ (effects' & chosen' .~ [eff & _before %~ (IndexedStackType Wildcard  (Just uniqueIdentifier):)] )

    return $ withoutIntersect $ executeEffs

  getStackEffects (Cast effs) = do 
    -- iopC "cast-effekts"
    unlessM (lift $ view allowCasts) $ throwing _CastsNotAllowed ()
    return $ withoutIntersect $ effsAsTuples effs

  getStackEffects (Assert effs forced) = do
    let beforeToAfter :: StackEffect -> StackEffect
        beforeToAfter eff = eff & _before .~ (eff ^. _after)
        effs' = bimap (map beforeToAfter) (map beforeToAfter) . view compOrExecIso $ effs

    -- iopC "assert-effekts"
    -- mapM (iopC . render . P.stackEffect) (effs' ^. chosen)

    when (has (chosen'.traverse._before._head) effs) $ throwing _MalformedAssert "No before arguments allowed"
    when (has (chosen'.traverse._streamArgs.traverse._Defining) effs) $ throwing _MalformedAssert "No defining arguments allowed!"
    when (has (chosen'.traverse._streamArgs.traverse._NotDefining._runtimeSpecified._Nothing) effs) $ throwing _MalformedAssert "Runtime Specification is Nothing!"
    when (has (chosen'.traverse._streamArgs.traverse._NotDefining._runtimeSpecified._Just._UnknownR) effs) $ throwing _MalformedAssert "Runtime Specification is UnknownR!"
    when (has (chosen'.traverse._streamArgs.traverse._NotDefining._runtimeSpecified._Just._NoR) effs) $ throwing _MalformedAssert "Runtime Specification is NoR!"
    when (has (chosen'.traverse._streamArgs.traverse._NotDefining._runtimeSpecified._Just._ResolvedR) effs) $ throwing _MalformedAssert "Runtime Specification is ResolvedR!"

    return $ withoutIntersect $ effsAsTuples $ effs' ^. from compOrExecIso

  getStackEffects (ColonExprClash n stackCommentEffects) = do
    let isForced = has (_Just._2.only True) stackCommentEffects
    when isForced $ do
       let effs = stackCommentEffects ^. _Just._1._semEffectsOfStack._stefwiMultiEffects._Wrapped
       lift $ exportColonDefinition isForced n effs False
    return emptyForthEffect


-- TODO forced effects possible even if colonexprclash
  getStackEffects (ColonExpr colonName stackCommentEffects bodyWords) = do

    let isForced = has (_Just._2.only True) stackCommentEffects
    whenM (lift $ (isForced &&) <$> (not <$> view allowForcedEffects)) $ throwing _ForcedEffectsNotAllowed ()

    lift $ modifyState $ set _currentCompiling True
    checkNodes <- view _1
    (effs, compI) <- if isForced then do 
              let forcedEffects = stackCommentEffects ^. _Just._1._semEffectsOfStack._stefwiMultiEffects._Wrapped
              let isIntersect = getAny $ stackCommentEffects ^. _Just._1._semEffectsOfStack._stefwiIntersection._Wrapped._Unwrapped
              return (forcedEffects, isIntersect)
            else (do
              (ForthEffect (compExecEffects, Intersections compI execI )) <- withEmpty' $ checkNodes bodyWords

              let (compColonEffects, execColonEffects) = unzip compExecEffects

              forceBeforesEmpty execColonEffects colonName
              forceAftersEmpty execColonEffects colonName

              effs <- (`runContT` return) $ callCC $ \ret -> do
                let stEffs' = preview (_Just._1._semEffectsOfStack._stefwiMultiEffects) stackCommentEffects
                case stEffs' of
                  Nothing -> ret compColonEffects
                  Just specifiedEffs -> do
                    let compositions :: [StackEffectPair]
                        compositions = liftM2 (,) compColonEffects (specifiedEffs ^. _Wrapped) 

                    let validCombinations = filter ((== min (lengthOf _Wrapped specifiedEffs) (length compColonEffects)) . length . group . map snd) . sequence . groupBy ((==) `on` fst) $ compositions
                        allOrAny = if compI then anyM else allM
                    stackCommentIsOK <- anyM (allOrAny (\(inferred,specified) -> lift $ inferred `effectMatches` specified)) validCombinations

                    if stackCommentIsOK then do
                        return $ specifiedEffs ^. _Wrapped
                    else  do

                        lift . lift $ throwing _NotMatchingStackComment colonName
              return (effs, compI))

    lift $ exportColonDefinition isForced colonName effs compI
    lift $ modifyState $ set _currentCompiling False

    return emptyForthEffect

  getStackEffects (Include _) = return emptyForthEffect
  getStackEffects (Require _) = return emptyForthEffect

  -- getStackEffects (BeginUntil tokens) = do
  --   checkNodes <- view _1
  --   (ForthEffect (effects,i)) <- withEmpty' $ checkNodes tokens

  --   newEffects <- lift $ forM effects (\(c,e) -> do { c' <- removeLastFlag c effects; return (c',e)})
  --   return $ withIntersect i newEffects

  --   where
  --    removeLastFlag eff effects = (`runContT` return) $ callCC $ \ret -> do
  --     lift $ when (eff & view (after.to length) & (/=1)) $ throwing _BeginUntilNoFlag (showEffects effects)
  --     -- lift $ iopC $ "last datatype is: " <> (show $ eff ^.. after._head._1)
  --     lift $ unlessM (lastDatatypeIsFlag eff) $ throwing _BeginUntilNoFlag (showEffects effects)
  --     return $ eff & after %~ tail


  --    lastDatatypeIsFlag eff = fmap (has $ _Just.only True) . runMaybeT $ do
  --      let mLastType = eff ^? (after._head._1)
  --      lastType <- hoistMaybe mLastType
  --      lift $ lastType `isSubtypeOf` (NoReference $ PrimType flag)
