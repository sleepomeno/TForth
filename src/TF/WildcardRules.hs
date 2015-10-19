{-# LANGUAGE  FlexibleContexts, NoMonomorphismRestriction #-}

module TF.WildcardRules (
    sameDegree
  , renameWildcards
  , oldWildcardDegreeIsGreater
  , newWildcardDegreeIsGreater
  , oldTopTypeNotWildcard
  , newTopTypeNotWildcard
  ) where 

import Control.Arrow 
import           Control.Lens hiding (noneOf,(??))
import           Control.Monad
import           Control.Monad.Cont
import           Control.Monad.Reader
import           Control.Monad.Writer
import           Control.Monad.Error.Lens
import  Text.PrettyPrint (render)

import           Control.Monad.State
import           TF.Util
import           TF.Types hiding (word, CheckerM')
import TF.HandleDegrees
import qualified TF.Printer as P
import TF.Type.StackEffect
import TF.Type.Nodes

import TF.Errors

renameWildcards :: CompExecEffect -> CompExecEffect -> CheckerM' (StackEffects, StackEffects)
renameWildcards = applyWildcardRule renameWildcards'
  where
      renameWildcards' :: WildcardRuleM StackEffects
      renameWildcards' = do
        (stE1, stE2) <- view storedEffects
        let wildcardsStE1 = getWildcards stE1 :: [IndexedStackType]
            wildcardsStE2 = getWildcards stE2 :: [IndexedStackType]

        iop "wildcardste1"
        iop $ show wildcardsStE1

        iop "wildcardste2"
        iop $ show wildcardsStE2

            -- maxIndex = maximum . map snd $ wildcardsStE1 ++ wildcardsStE2
        let maxIndex = maximum . (0:) . toListOf (traverse._2._Just) $ wildcardsStE1 ++ wildcardsStE2
            wildcardIndicesMatch x y = guard (snd x == snd y) >> Just x

        let wildcardMatches :: [Maybe IndexedStackType]
            wildcardMatches = map (uncurry wildcardIndicesMatch) $ liftM2 (,) wildcardsStE1 wildcardsStE2 

        -- iop "wildcardmatches"
        -- iop $ show wildcardMatches

        -- sameWildcard <- hoistEither $ note (stE1, stE2)  (preview (traverse._Just) wildcardMatches )
        sameWildcard <-  preview (traverse._Just) wildcardMatches & orReturnEffects 

        logApplication "renameWildcards"

        -- let setNewIndex  = sameWildcard & _2 ?~ (maxIndex + 1)
        let hasSameWildcard (t,i') = i' == sameWildcard ^. _2 && baseType t == baseType (sameWildcard ^. _1)
            performSubstitution eff = eff & _before.mapped.filtered hasSameWildcard._2 ?~ maxIndex+1
                                          & _after.mapped.filtered hasSameWildcard._2  ?~ maxIndex+1
        modify (fmap performSubstitution)
        local ((storedEffects._2) .~ performSubstitution stE2) renameWildcards'
    
sameDegree :: CompExecEffect -> CompExecEffect -> CheckerM' (StackEffects, StackEffects)
sameDegree = applyWildcardRule sameDegree'
  where
   -- Both are wildcards. m == n
      sameDegree' :: WildcardRuleM StackEffects 
      sameDegree' = do
        (stE1, stE2) <- view storedEffects
        topOfStackIndexed@(topOfStack, _) <-  firstOf (_after.traverse) stE1 & orReturnEffects
        topOfArgsIndexed@(topOfArgs,topOfArgsIndex) <-  firstOf (_before.traverse) stE2 & orReturnEffects 

        assert (isWildcard topOfStackIndexed && isWildcard topOfArgsIndexed) 
        let stE2wildcards = getWildcards stE2

        assert (topOfStackIndexed `notElem` stE2wildcards)

        let m = refDegree topOfStack
        let n = refDegree topOfArgs

        assert (m == n)

        logTopTypes topOfStackIndexed topOfArgsIndexed "sameDegree"

        when (hasUnknownBaseType topOfStack) $
            addTypeInfo topOfArgs topOfStackIndexed

        let substitutor = first baseType topOfStackIndexed
            shouldBeSubstituted t = isWildcard t && getIndex t == topOfArgsIndex
            performSubstitution eff = eff & _before.mapped.filtered shouldBeSubstituted .~ substitutor
                                      & _streamArgs.traverse._Defining._argType._Just.filtered shouldBeSubstituted .~ substitutor
                                  & _after.mapped.filtered shouldBeSubstituted .~ substitutor
        modify (fmap performSubstitution)
        local ((storedEffects._1) .~ (stE1 & _after %~ tail) >>>
               (storedEffects._2) .~ (performSubstitution stE2 & _before %~ tail)) $ sameDegree' 


oldWildcardDegreeIsGreater :: CompExecEffect -> CompExecEffect -> CheckerM' (StackEffects, StackEffects)
oldWildcardDegreeIsGreater = applyWildcardRule oldWildcardDegreeIsGreater'
   where
     {-
Both tops are wildcards. topofstack kommt nicht in stE2 vor und m > n
     -}
      oldWildcardDegreeIsGreater' :: WildcardRuleM StackEffects
      oldWildcardDegreeIsGreater' = do 
        (stE1, stE2) <- view storedEffects
        topOfStackIndexed@(topOfStack, topOfStackIndex) <-  firstOf (_after.traverse) stE1 & orReturnEffects
        topOfArgsIndexed@(topOfArgs, topOfArgsIndex) <-  firstOf (_before.traverse) stE2 & orReturnEffects
        iopW "top of stack indexed"
        iopW $ show topOfStackIndexed

        iopW "top of args indexed"
        iopW $ show topOfArgsIndexed

        assert (isWildcard topOfStackIndexed && isWildcard topOfArgsIndexed)
        let stE2wildcards = getWildcards stE2

        assert (topOfStackIndexed `notElem` stE2wildcards)

        let m = refDegree topOfStack
        let n = refDegree topOfArgs

        assert (m > n)

        logTopTypes topOfStackIndexed topOfArgsIndexed "oldWildcardDegreeIsGreater"
        iopW $ "show stored effects"
        iopW $ show $ (stE1, stE2)

        adjustReferenceDegreeOfPossibleUnknownType topOfArgs (m-n) n
        when (hasUnknownBaseType topOfStack) $
            addTypeInfo topOfArgs topOfStackIndexed
        wildcardType <- getWildcardBaseType topOfStack topOfArgs

        let substitutor = first ((!! (m-n)) . iterate Reference . setBaseType wildcardType) (baseType topOfStack, topOfStackIndex)
            performSubstitution eff = eff & _before.mapped.likeArgsIndex .~ substitutor &
                         _after.mapped.likeArgsIndex .~ substitutor  
                          -- & _streamArgs.traverse._Defining._argType._Right.likeArgsIndex .~ substitutor
                         & _streamArgs.traverse._Defining._argType._Just.likeArgsIndex .~ substitutor
            likeArgsIndex = filtered (\wc -> isWildcard wc && getIndex wc == topOfArgsIndex) 
        modify (fmap performSubstitution)
        let modifyReader = ((storedEffects._1) .~ (stE1 & _after %~ tail) >>>
               (storedEffects._2) .~ (stE2 & _before %~ tail
                                           & _before.mapped.likeArgsIndex .~ substitutor 
                                           & _after.mapped.likeArgsIndex .~ substitutor
                                           -- & _streamArgs.traverse._Defining._argType._Left._Just.likeArgsIndex .~ substitutor
                                           & _streamArgs.traverse._Defining._argType._Just.likeArgsIndex .~ substitutor
                                           -- & _streamArgs.traverse._Defining._argType._Right.likeArgsIndex .~ substitutor
                                     ))
        iopW $ "show MODIFIED stored effects"
        iopW $ show . fst $ modifyReader ((stE1, stE2), undefined)
        local modifyReader $ oldWildcardDegreeIsGreater'


newWildcardDegreeIsGreater :: CompExecEffect -> CompExecEffect -> CheckerM' (StackEffects, StackEffects)
newWildcardDegreeIsGreater = applyWildcardRule newWildcardDegreeIsGreater'
  where
     {-
Both tops are wildcards. topofstack kommt nicht in stE2 vor und m < n
     -}
      newWildcardDegreeIsGreater' :: WildcardRuleM StackEffects
      newWildcardDegreeIsGreater' = do 
        (stE1, stE2) <- view storedEffects
        topOfStackIndexed@(topOfStack,topOfStackIndex) <-  firstOf (_after.traverse) stE1 & orReturnEffects
        topOfArgsIndexed@(topOfArgs,topOfArgsIndex) <-  firstOf (_before.traverse) stE2 & orReturnEffects

        assert (isWildcard topOfStackIndexed && isWildcard topOfArgsIndexed)
        let stE2wildcards = getWildcards stE2

        assert (topOfStackIndexed `notElem` stE2wildcards)
        let m = refDegree topOfStack
        let n = refDegree topOfArgs

        assert (m < n) 

        logTopTypes topOfStackIndexed topOfArgsIndexed "newWildcardDegreeIsGreater"


        adjustReferenceDegreeOfPossibleUnknownType topOfStack (n-m) m
        wildcardType <- getWildcardBaseType topOfStack topOfArgs

        iopW $ "base wildcardtype is:"
        iopW $ show wildcardType

        let setBaseWildcardType = setBaseType wildcardType

        let adjustReferenceType = first $ (!! (n-m)) . iterate Reference . setBaseWildcardType
            adjustBaseWildcardType = over _1 setBaseWildcardType 

        let substitutor :: IndexedStackType
            substitutor = adjustReferenceType (baseType topOfArgs, topOfArgsIndex)
                           
            isTopOfStackType wc = isWildcard wc && getIndex wc == topOfStackIndex
            isTopOfArgsType wc = isWildcard wc && getIndex wc == topOfArgsIndex

        -- let stE1' = stE1 & _streamArgs.traverse._Defining._argType._Right.filtered isTopOfStackType %~ adjustReferenceType & _streamArgs.traverse._Defining._argType._Left._Just.filtered isTopOfStackType %~ adjustReferenceType
        let stE1' = stE1
         -- & _streamArgs.traverse._Defining._argType._Right.filtered isTopOfStackType %~ adjustReferenceType
                                    & _streamArgs.traverse._Defining._argType._Just.filtered isTopOfStackType %~ adjustReferenceType
                         & _after %~ tail & _after.mapped.filtered isTopOfStackType .~ substitutor
                         & _before.mapped.filtered isTopOfStackType .~  substitutor


        local ((storedEffects._1) .~ stE1' >>>
               (storedEffects._2) .~ (stE2 & _before %~ tail
                                           & _after.mapped.filtered isTopOfArgsType %~ adjustBaseWildcardType)) newWildcardDegreeIsGreater'


oldTopTypeNotWildcard :: CompExecEffect -> CompExecEffect -> CheckerM' (StackEffects, StackEffects)
oldTopTypeNotWildcard = applyWildcardRule oldTopTypeNotWildcard'
  where
    -- theorem 5
    oldTopTypeNotWildcard' :: WildcardRuleM StackEffects
    oldTopTypeNotWildcard' = do
        (stE1, stE2) <- view storedEffects

        topOfStackIndexed@(topOfStack,topOfStackIndex) <-  firstOf (_after.traverse) stE1 & orReturnEffects
        topOfArgsIndexed@(topOfArgs,topOfArgsIndex) <-  firstOf (_before.traverse) stE2 & orReturnEffects

        assert (not . isWildcard $ topOfStackIndexed)
        assert (isWildcard topOfArgsIndexed)

        let m = refDegree topOfStack
            n = refDegree topOfArgs

        assert (m >= n)

        logTopTypes topOfStackIndexed topOfArgsIndexed "oldTopTypeNotWildcard"

        let substitutor = topOfStackIndexed & _1 %~ removeDegree n -- & makeResolved

            adjustSte2 eff = eff & _before.mapped.filtered isTopOfArgsType .~ substitutor
                                 & _after.mapped.filtered isTopOfArgsType .~ substitutor
                                 -- & _streamArgs.traverse._Defining._argType._Right.filtered (== topOfArgsIndexed) .~ topOfStackIndexed
                                 & _streamArgs.traverse._Defining._argType._Just.filtered (== topOfArgsIndexed) .~ topOfStackIndexed
            isTopOfArgsType wc = isWildcard wc && getIndex wc == topOfArgsIndex


            stE2' = stE2 & _before %~ tail & adjustSte2

        addTypeInfo topOfArgs topOfStackIndexed
        modify (fmap adjustSte2)

        local ((storedEffects._1._after) %~ tail >>>
               (storedEffects._2) .~ stE2') oldTopTypeNotWildcard' 


newTopTypeNotWildcard :: CompExecEffect -> CompExecEffect -> CheckerM' (StackEffects, StackEffects)
newTopTypeNotWildcard = applyWildcardRule newTopTypeNotWildcard'
  where
     newTopTypeNotWildcard' :: WildcardRuleM StackEffects  
     newTopTypeNotWildcard' = do
        (stE1, stE2) <- view storedEffects

        topOfStackIndexed@(topOfStack,topOfStackIndex) <-  firstOf (_after.traverse) stE1 & orReturnEffects
        topOfArgsIndexed@(topOfArgs,topOfArgsIndex) <-  firstOf (_before.traverse) stE2 & orReturnEffects

        assert (isWildcard topOfStackIndexed) 
        assert (not $ isWildcard topOfArgsIndexed)

        let m = refDegree topOfStack
            n = refDegree topOfArgs

        assert (m <= n)

        logTopTypes topOfStackIndexed topOfArgsIndexed "newTopTypeNotWildcard"

        addTypeInfo topOfStack topOfArgsIndexed

        let substitutor ::  IndexedStackType
            substitutor = topOfArgsIndexed & _1 %~ removeDegree m
            substituteBaseType (t, i) = (setBaseType (baseType topOfArgs) t, topOfArgsIndex) & _1 %~ removeDegree m
            isTopOfStackType wc = isWildcard wc && getIndex wc == topOfStackIndex
            
        local (storedEffects._1._after %~ tail >>>
               storedEffects._2._before %~ tail >>>
               -- storedEffects._1._after.mapped.filtered isTopOfStackType .~ substitutor >>>
               -- storedEffects._1._before.mapped.filtered isTopOfStackType .~ substitutor) newTopTypeNotWildcard' 
               storedEffects._1._after.mapped.filtered isTopOfStackType %~ substituteBaseType >>>
               storedEffects._1._before.mapped.filtered isTopOfStackType %~ substituteBaseType) newTopTypeNotWildcard' 

hasUnknownBaseType = has _UnknownType . baseType
addTypeInfo possibleUnknownType concreteType = when (hasUnknownBaseType possibleUnknownType) $  do 
          resolveUnknown ((baseType possibleUnknownType) ^?! _UnknownType) (first baseType concreteType)

adjustReferenceDegreeOfPossibleUnknownType :: DataType -> Int -> t -> WildcardRuleM ()
adjustReferenceDegreeOfPossibleUnknownType topOfStack diff currentRefDegree = do

  when (has _UnknownType (baseType topOfStack)) $ do
       lift . lift $ tell [(ReferenceDegree identifier diff)] 
  where
    identifier = baseType topOfStack ^?! _UnknownType
    isUnknownType = isCorrectCreatedWord identifier 
    isTarget = isUnknownType 

isCorrectCreatedWord identifier (w, _)  = has _UnknownType (baseType w)  && ((baseType w ^?! _UnknownType) == identifier)

  

resolveUnknown :: Identifier -> IndexedStackType -> WildcardRuleM ()
resolveUnknown identifier (arg,_) = blocked $ do
  iopW $ "RRRRRRRRRRRRRR"
  lift . lift $ tell [(ResolveUnknown identifier arg)] 

updateFields :: (StackEffect -> StackEffect) -> ClassName -> [(Variable, OOFieldSem)] -> [(Variable, OOFieldSem)]
updateFields updateStackEffect _ fields = for fields $ second (fmap updateStackEffect) 

isWildcard :: IndexedStackType -> Bool
isWildcard (t, _) = isWildcard' t

isWildcard' (WildcardWrapper) = True
isWildcard' (Wildcard) = True
isWildcard' (Dynamic) = True
isWildcard' (UnknownType _) = True
isWildcard' (Reference x) = isWildcard' x
isWildcard' _ = False


getWildcardBaseType :: DataType -> DataType -> WildcardRuleM DataType
getWildcardBaseType t1 t2 = do
  when (not $ isWildcard' t1 && isWildcard' t2) $
     l3 $ throwing _Impossible "Both must be wildcards"
  return $ case (baseType t1) of
            Wildcard -> case (baseType t2) of
                           UnknownType i -> UnknownType i
                           _             -> Wildcard
            WildcardWrapper -> case (baseType t2) of
                           UnknownType i -> UnknownType i
                           _             -> WildcardWrapper
            UnknownType i -> UnknownType i
            Dynamic -> case (baseType t2) of
                           UnknownType i -> UnknownType i
                           x           -> x

getWildcards stE = filter isWildcard $ (view _before stE) ++ (view _after stE) -- ++ filter isWildcard (toListOf (_streamArgs.traverse._Defining._argType._Just) stE)

type CheckerM' = WriterT [ChangeState] CheckerM
type ContinuationM =  ContT StackEffects (StateT (Maybe StackEffect) (WriterT [ChangeState] CheckerM)) 
type ContinuationM' = ContT StackEffects (WriterT [ChangeState] CheckerM) 
type Return z = StackEffects -> ContinuationM z
type WildcardRuleM  = ReaderT (StackEffects, Return IndexedStackType ) ContinuationM 
type WildcardRuleM' = ReaderT (StackEffects, Return IndexedStackType ) ContinuationM'

storedEffects = _1
exitContinuation = _2

logApplication rule = blocked $ do
  iopW $ "APPLY " ++ rule 

showType = render . P.dataType

logTopTypes topOfStackIndexed topOfArgsIndexed rule = blocked $ do 
  iopW $ "APPLY " ++ rule
  iopW $ "Top of stack: " ++ showType topOfStackIndexed
  iopW $ "Top of args : " ++ showType topOfArgsIndexed

orReturnEffects  m  = do
  (stE1, stE2) <- view storedEffects 
  returnEffects' <- view exitContinuation  
  case m of
   Just x -> return x
   Nothing -> lift $ returnEffects' (stE1, stE2)

returnEffects = do
  effs <- view storedEffects
  exit <- view exitContinuation  -- :: A (B IndexedStackType)
  lift $ exit effs

assert b = unless b $ void $ returnEffects
  
applyWildcardRule rule (oldComp', oldExec') (newComp', newExec')  = do
  ((oldExec, newExec), Just newComp) <- unwrapWith (Just newComp') (oldExec', newExec') rule 
  ((oldComp, newComp'), _) <- unwrapWith Nothing (oldComp', newComp) rule
  return ((oldComp, oldExec), (newComp', newExec))
  where 
    unwrapWith maybeRuntimeEffect storedEffects' wildcardApplication = (`runStateT` maybeRuntimeEffect) . (`runContT` return) $ callCC $ \exit -> (`runReaderT` (storedEffects',exit)) wildcardApplication

applyWildcardRule' rule (oldComp', oldExec') (newComp', newExec')  = do
  ((oldExec, newExec), Just newComp) <- unwrapWith (Just newComp') (oldExec', newExec') rule 
  ((oldComp, newComp'), _) <- unwrapWith Nothing (oldComp', newComp) rule
  return ((oldComp, oldExec), (newComp', newExec))
  where 
    unwrapWith maybeRuntimeEffect storedEffects' wildcardApplication = (`runStateT` maybeRuntimeEffect) . (`runContT` return) $ callCC $ \exit -> (`runReaderT` (storedEffects',exit)) wildcardApplication

