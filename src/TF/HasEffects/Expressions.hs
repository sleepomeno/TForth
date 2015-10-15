{-# LANGUAGE FlexibleContexts, NoMonomorphismRestriction, LambdaCase  #-}

module TF.HasEffects.Expressions (getStackEffects) where

import           Control.Error            as E
import           Control.Lens             hiding (noneOf, (??), _Empty)
import           Control.Monad.Error.Lens
import           Control.Monad.Extra
import           Control.Monad.Reader
import           Control.Monad.Cont
import           Text.PrettyPrint         (render)
import Data.Function (on)

import           Data.List
import           TF.Util
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

instance HasStackEffects Expr where

  getStackEffects (ControlExpr x) = CS.getStackEffects' x

  getStackEffects (OOPExpr x) = OOP.getStackEffects' x

  getStackEffects (Postpone _) = return emptyForthEffect

  getStackEffects (PostponeImmediate w) = do
    getStackEffects w

  getStackEffects (Interpreted forthWordsOrExprs) = do
    lift $ modifyState $ set currentCompiling False
    lift $ depth += 1
    checkNodes <- view _1
    compExecEffs <- withEmpty' $ checkNodes forthWordsOrExprs
    lift $ depth -= 1
    lift $ modifyState $ set currentCompiling True
    return compExecEffs

  getStackEffects (Create create init does) = do
    uniqueId <- identifier <<+= 1


    checkNodes <- view _1
    let go :: (Node, [Node], Maybe Node, Maybe [Node]) -> CheckerM ForthEffect
        go (create, exprs, comma, does) = withEmpty $ do
          checkNodes (create : exprs)

          runMaybeT $ do
            c <- hoistMaybe comma
            lift $ checkNodes [c]
          result <- view effects <$> getState

          maybeDoes <- runMaybeT $ do
            exprs' <- hoistMaybe does
            forthEff <- lift $ withEmpty $ checkNodes exprs'
            return $ forthEff ^. _Wrapped._1

          result' <- case maybeDoes of
                        Nothing -> return result
                        Just doesEffects -> do
                          -- let newCreating = create & (elementOf (_ForthWord.l.traverse.streamArgs.traverse._Defining) 0).runtimeEffect ?~ _RuntimeNotProcessed # (doesEffects & traverse.both %~ (\(StackEffect x y z) -> (x,y,z)))
                          let newCreating = create & elementOf (_ForthWord.l.traverse.streamArgs.traverse._Defining) 0.runtimeEffect ?~ doesEffects
                          go (newCreating, exprs, comma, Nothing)



          return result'
  
    withEmpty' $ do
      lift $ depth += 1
      cr <- checkNodes [create]

      maybeInitType <- runMaybeT $ (do
        (exprs, comma) <- hoistMaybe init
        lift $ checkNodes exprs
        stEffs <- lift $ effectsOfState
        let typeOfCreated :: Maybe IndexedStackType
            typeOfCreated = stEffs ^?! _head & preview (after._head)

        -- when (typeOfCreated == Nothing) $ iop "UNGLEICH NOTHING"

        lift $ checkNodes [comma]


        effs <- lift effectsOfState
        -- iopC "Current State:\n"
        -- liftIO $ mapM_ (putStrLn . render . P.stackEffect) effs
        maybe (liftUp . lift  $ preview (_head.before._head) effs E.?? (_Impossible # "No top stack value in maybeInitType")) return typeOfCreated) :: CheckerM (Maybe IndexedStackType)

      result <- case maybeInitType of
                    Nothing -> go (create, [], Nothing, does)
                    Just initType -> do
                      let newCreating = create & elementOf (_ForthWord.l.traverse.streamArgs.traverse._Defining) 0.argType ?~ initType
                      go (newCreating, init ^?! _Just._1, init ^? _Just._2, does)

      effs <- effectsOfState
      iopC "Show effects of create:\n"
      showEffs' effs
      lift $ depth -= 1
      return result

    where
       l = if has (_ForthWord._DefE) create then
             _DefE.chosen._2
           else
             _KnownWord.stacksEffects.chosen''._Wrapped

    -- iopC "Show effects of create:\n"
    -- liftIO $ mapM_ (putStrLn . render . P.stackEffect) effs

    -- iopC $ "The Create-----\n"
    -- iopC $ render . either P.forthWord P.expr $ create

  getStackEffects (ColonExprImmediate colonName stackCommentEffects bodyWords) = getStackEffects (ColonExpr colonName stackCommentEffects bodyWords)


  getStackEffects (Tick effects pw) = do
    unless (length effects == 1) $ throwing (_ErrorTick . _MultipleEffects) () 
    let effect = effects ^?! _head
    when (has (before._head) effect) $ throwing (_ErrorTick . _MalformedAssert) "No before allowed!"
    when (has (after._head) effect) $ throwing (_ErrorTick . _MalformedAssert) "No After allowed!"
    let args = toListOf (streamArgs.traverse._NotDefining.runtimeSpecified._Just._KnownR) effect
    unless (1 == length args) $ throwing (_ErrorTick . _MalformedAssert) "Exactly one knownR stream argument necessary!"

    let runtimeEff'' = args ^?! _head -- .stackEffectIso

    let pw' = pw & stacksEffects._CompiledEff._Wrapped.traverse.streamArgs.traverse._NotDefining.runtimeSpecified._Just %~ setEffect
        setEffect :: RuntimeSpecification -> RuntimeSpecification
        setEffect = \case
          UnknownR i -> ResolvedR i runtimeEff''-- (effect ^. from stackEffectIso)
          x          -> x
    let resolvedRuntimes = pw' ^.. stacksEffects._CompiledEff._Wrapped.traverse.streamArgs.traverse._NotDefining.runtimeSpecified._Just._ResolvedR :: [(UniqueArg, StackEffect)]
        pw'' = pw' & stacksEffects._CompiledEff._Wrapped.traverse %~ ((before.traverse %~ resolveRuntimeType resolvedRuntimes) . (after.traverse %~ resolveRuntimeType resolvedRuntimes))

    getStackEffects (KnownWord pw'')

  getStackEffects (Execute effects') = do
    iop "getStackEffects Execute"
    let effects = effects' ^. chosen
    unless (length effects == 1) $ throwing (_ErrorE . _MultipleEffects) () 
    let effect = effects ^?! _head
    when (has (before._head) effect) $ throwing (_ErrorE . _MalformedAssert) "No before allowed!"
    unless (1 == length (view after effect)) $ throwing (_ErrorE . _MalformedAssert) "Exactly One After data type!"
    let xts = toListOf (after.traverse._1._NoReference._ExecutionType.runtimeSpecified._Just._KnownR) effect
    unless (1 == length xts) $ throwing (_ErrorE . _MalformedAssert) "Exactly one xt data type!"

    let eff = xts ^?! _head

    let compOrExec = if has _Compiled effects' then (_Compiled #) else (_Executed #)

    collectEffects <- view _3
    lift $ collectEffects (_Expr # Assert effects' False) -- TODO take forced from parsed assertion

    uniqueIdentifier <- lift $ identifier <<+= 1
    let executeEffs = effsAsTuples $ compOrExec [eff & before %~ ((Wildcard, Just uniqueIdentifier):)] 

    return $ withoutIntersect $ executeEffs

  getStackEffects (Cast effs) = do 
    -- iopC "cast-effekts"
    unlessM (lift $ view allowCasts) $ throwing _CastsNotAllowed ()
    return $ withoutIntersect $ effsAsTuples effs

  getStackEffects (Assert effs forced) = do
    let beforeToAfter :: StackEffect -> StackEffect
        beforeToAfter eff = eff & before .~ (eff ^. after)
        effs' = bimap (map beforeToAfter) (map beforeToAfter) effs

    -- iopC "assert-effekts"
    -- mapM (iopC . render . P.stackEffect) (effs' ^. chosen)

    when (has (chosen.traverse.before._head) effs) $ throwing _MalformedAssert "No before arguments allowed"
    when (has (chosen.traverse.streamArgs.traverse._Defining) effs) $ throwing _MalformedAssert "No defining arguments allowed!"
    when (has (chosen.traverse.streamArgs.traverse._NotDefining.runtimeSpecified._Nothing) effs) $ throwing _MalformedAssert "Runtime Specification is Nothing!"
    when (has (chosen.traverse.streamArgs.traverse._NotDefining.runtimeSpecified._Just._UnknownR) effs) $ throwing _MalformedAssert "Runtime Specification is UnknownR!"
    when (has (chosen.traverse.streamArgs.traverse._NotDefining.runtimeSpecified._Just._NoR) effs) $ throwing _MalformedAssert "Runtime Specification is NoR!"
    when (has (chosen.traverse.streamArgs.traverse._NotDefining.runtimeSpecified._Just._ResolvedR) effs) $ throwing _MalformedAssert "Runtime Specification is ResolvedR!"

    return $ withoutIntersect $ effsAsTuples effs'

  getStackEffects (ColonExprClash n stackCommentEffects) = do
    let isForced = has (_Just._2.only True) stackCommentEffects
    when isForced $ do
       let effs = (stackCommentEffects & view (_Just._1.effectsOfStack._Wrapped))
       lift $ exportColonDefinition isForced n effs False
    return emptyForthEffect


-- TODO forced effects possible even if colonexprclash
  getStackEffects (ColonExpr colonName stackCommentEffects bodyWords) = do

    iopC $ "in colonexpr getstackeffects"
    iopC $ show stackCommentEffects

    -- iopC $ "bodywords"

    -- liftIO $ putStrLn . render . P.pprint $ bodyWords
    -- iopC $ "before in colonexpr"
    -- compExecEffects <- fromEmptyStack $ checkNodes bodyWords
    let isForced = has (_Just._2.filtered id) stackCommentEffects
    whenM (lift $ (isForced &&) <$> (not <$> view allowForcedEffects)) $ throwing _ForcedEffectsNotAllowed ()

    lift $ modifyState $ set currentCompiling True
    lift $ depth += 1
    checkNodes <- view _1
    (effs, compI) <- if isForced then
             return ((stackCommentEffects & view (_Just._1.effectsOfStack._Wrapped)), False)
            else (do
              (ForthEffect (compExecEffects, Intersections compI execI )) <- withEmpty' $ checkNodes bodyWords

              let compColonEffects = (compExecEffects ^.. traverse._1)
                  execColonEffects = (compExecEffects ^.. traverse._2)

              forceBeforesEmpty execColonEffects colonName
              forceAftersEmpty execColonEffects colonName

              -- effs <- liftM (view chosen) . runEitherT  $ do
              effs <- (`runContT` return) $ callCC $ \ret -> do
                let stEffs' = view (_1.effectsOfStack._Wrapped) <$> stackCommentEffects
                when (isNothing stEffs') $ ret compColonEffects

                let specifiedEffs = stEffs' ^?! _Just

                -- let validCombinations = filter ((const True) . length . group . map snd) . sequence . groupBy ((==) `on` fst) $ liftM2 (,) compColonEffects specifiedEffs 
                let validCombinations = filter ((== min (length specifiedEffs) (length compColonEffects)) . length . group . map snd) . sequence . groupBy ((==) `on` fst) $ liftM2 (,) compColonEffects specifiedEffs 
                -- let validCombinations' =  liftM2 (,) compColonEffects specifiedEffs 
                -- let validCombinations'' = sequence $ groupBy ((==) `on` fst) $ liftM2 (,) compColonEffects specifiedEffs 
                    allOrAny = if compI then anyM else allM
                -- stackCommentIsOK <- allM (\x -> anyM (\y -> do
                --   lift $ y `effectMatches` x) compColonEffects) specifiedEffs
                stackCommentIsOK <- anyM (allOrAny (\(inferred,specified) -> lift $ inferred `effectMatches` specified)) validCombinations
                -- iop $ "length validCombinations: " <> (show $ length validCombinations)
                -- mapM (\[(a,b), (c,d)] -> iop "newtuple" >> showEff c >> showEff d) validCombinations''
                -- stackCommentIsOK <- anyM (allM (\(inferred,specified) -> do

                --      iop "inferred"
                --      showEffs' [inferred]
                --      iop "specified"
                --      showEffs' [specified]
                --      lift $ specified `effectMatches` inferred)) validCombinations
                  -- lift $ y `effectIsSubtypeOf` x) compColonEffects) specifiedEffs

                if stackCommentIsOK then do
                    return specifiedEffs
                else  do

                    -- iop $ "validCombinations"
                    iop $ "compcolon EFFEKTE:"
                   
                    (mapM_ (iopC . render . P.stackEffect) $ compColonEffects )

                    iop $ "> spezifizierte EFFEKTE:"
                    mapM_ (iopC . render . P.stackEffect) specifiedEffs 
                    -- lift . lift . lift $ E.left $ "Stack comment does not match in word " ++ colonName
                    lift . lift $ throwing _NotMatchingStackComment colonName
              return (effs, compI))

    lift $ exportColonDefinition isForced colonName effs compI

    lift $ modifyState $ set currentCompiling False

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
