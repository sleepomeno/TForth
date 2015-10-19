module TF.SubtypeUtil where

import           Control.Arrow
import           Control.Error            as E
import           Control.Lens             hiding (noneOf, (??), _Empty)
import           Control.Monad.Extra
import           Control.Monad.Reader
import           Control.Monad.Writer
import           Control.Monad.Cont
import           TF.ForthTypes as FT

import qualified Data.Set as S
import           TF.Util
import           Text.Parsec              hiding (token)
import           TF.Types                 hiding (isSubtypeOf, word)
import TF.HandleDegrees
import TF.Type.StackEffect
import TF.Type.Nodes

isSubtypeOf :: DataType -> DataType -> CheckerM Bool
isSubtypeOf t1 t2 = do
  subtypeRelationSet <- view subtypeRelation <$> getState :: CheckerM (S.Set (BasicType, BasicType))
  if refDegree t1 == refDegree t2 then do
    let baseType1 = baseType t1  :: DataType
        baseType2 = baseType t2
        -- bothNotWildcard = has _NoReference baseType1 && has _NoReference baseType2
        -- subtypeOfWildcard = ((not (has _Wildcard baseType1) && has _Wildcard baseType2)) || ((not (has _WildcardWrapper baseType1) && has _WildcardWrapper baseType2)) || (has _Wildcard baseType1 && has _Wildcard baseType2) || (has _Dynamic baseType1 || has _Dynamic baseType2 || has (_NoReference._PrimType.symbol.only DYN) baseType1 || has (_NoReference._PrimType.symbol.only DYN) baseType2)
        subtypeOfWildcard = ((not (has _Wildcard baseType1) && has _Wildcard baseType2)) || ((not (has _WildcardWrapper baseType1) && has _WildcardWrapper baseType2)) || (has _Wildcard baseType1 && has _Wildcard baseType2) || (has _Dynamic baseType1 || has _Dynamic baseType2 || has (_NoReference._PrimType._primtypeSymbol.only DYN) baseType1 || has (_NoReference._PrimType._primtypeSymbol.only DYN) baseType2)
        subtypeOfXT :: Bool
        subtypeOfXT = fromMaybe False $ do
          r1 <- baseType1  ^? _NoReference._ExecutionType._exectokenRuntimeSpecified._Just
          r2 <- baseType2 ^? _NoReference._ExecutionType._exectokenRuntimeSpecified._Just
          r1' <- (r1 ^? _KnownR) `mplus` (r1 ^? _ResolvedR._2)
          r2' <- (r2 ^? _KnownR) `mplus` (r2 ^? _ResolvedR._2)
          return $ r1' == r2'
        inSubtypeRelation = fromMaybe False $ do
          type1 <- baseType1 ^? _NoReference
          type2 <- baseType2 ^? _NoReference
          return $ S.member (type1, type2) subtypeRelationSet

    -- iop "Type 1"
    -- let t1' = P.dataType $ ((baseType1, Nothing) :: IndexedStackType)
    -- iop $ render t1'
    -- iop $ "has dynamic: " ++ show (has _Dynamic baseType1)
    -- iop "Type 2"
    -- let t2' = P.dataType $ ((t2, Nothing) :: IndexedStackType)
    -- iop $ render t2'

    return $ subtypeOfXT || inSubtypeRelation || subtypeOfWildcard
  else return False 

getCommonSupertype effs1 effs2 = do
  guard1 <- allM (\(x1, x2) -> anyM (\(y1, y2) -> do
    res1 <- y1 `effectIsSubtypeOf` x1
    res2 <- y2 `effectIsSubtypeOf` x2
    return res1) effs1) effs2
  guard2 <- allM (\(x1, x2) -> anyM (\(y1, y2) -> do
    res1 <- y1 `effectIsSubtypeOf` x1
    res2 <- y2 `effectIsSubtypeOf` x2
    return $ res1) effs2) effs1
  return $ msum [(guard guard1) >> Just effs1, (guard guard2) >> Just effs2]

getCommonSupertype' effs1 effs2 = do
  guard1 <- allM (\x1 -> anyM (\y1 -> do
    res1 <- y1 `effectIsSubtypeOf` x1
    return $ res1) effs1) effs2
  guard2 <- allM (\x1 -> anyM (\y1 -> do
    res1 <- y1 `effectIsSubtypeOf` x1
    return $ res1) effs2) effs1
  return $ msum [(guard guard1) >> Just effs1, (guard guard2) >> Just effs2]

getCommonSupertype''
  :: [[StackEffect]]
     -> ParsecT
          [Token] ParseState StackEffectM (Maybe [StackEffect])
getCommonSupertype'' effs = runMaybeT $ foldM (\result another -> do
                                      sup <- lift $ getCommonSupertype' result another
                                      hoistMaybe sup) (head effs) (tail effs)
constraints :: StackEffect -> [(Int, Int)]
constraints stEff =
  [(i,i') | (i , (type1, typeIndex1)) <- typeByPosition,
            (i', (type2, typeIndex2)) <- typeByPosition,
             type1 == type2,
             typeIndex1 == typeIndex2,
             i /= i', typeIndex1 /= Nothing] 
   where
     consuming = stEff ^. _before
     producing = stEff ^. _after
     streamArguments = stEff ^.. _streamArgs.traverse._Defining._argType._Just
     typeByPosition :: [(Int, IndexedStackType)]
     typeByPosition = zip [0..] (consuming ++ streamArguments ++ producing)
     
      

effectIsSubtypeOf :: StackEffect -> StackEffect -> CheckerM Bool
effectIsSubtypeOf eff1 eff2 =  (`runContT` id) $ callCC $ \exit -> do
  let (before1, before2) = (view _before *** view _before) $ (eff1, eff2)
      (after1, after2)   = (view _after *** view _after) $ (eff1, eff2)
      (streamArgs1, streamArgs2)   = (view _streamArgs *** view _streamArgs) $ (eff1, eff2)
      -- (allTypes1, allTypes2) = (allTypes *** allTypes) $ (eff1, eff2)
      sameLengths = (length before1 == length before2) && (length after1 == length after2) && (length streamArgs1 == length streamArgs2) -- && (length (allTypes1 ^. _1) == length (allTypes2 ^. _1)) && (length (allTypes2 ^. _2) == length (allTypes1 ^. _2))
      streamArgsSameKind = all (\(arg1,arg2) -> (has _NotDefining arg1 && has _NotDefining arg2) ||
                                                (has (_Defining._argType._Just) arg1 && has (_Defining._argType._Just) arg2) ||
                                                (has (_Defining._argType._Nothing) arg1 && has (_Defining._argType._Just) arg2) ||
                                                (has (_Defining._argType._Nothing) arg1 && has (_Defining._argType._Nothing) arg2)) $ zip streamArgs1 streamArgs2 :: Bool


  -- iop "before argskind"
  when (not $ sameLengths && streamArgsSameKind) $ exit (return False)
  -- iop "after argskind"

  forM_ (zip before1 before2) $ \((t1,_),(t2,_)) -> do
    isContravariant <- lift $ t2 `isSubtypeOf` t1
    iop $ "iscontravariant: " ++ show isContravariant
    when (not isContravariant) $ exit (return False)
  iop "FUUUU"

  forM_ (zip after1 after2) $ \((t1,_),(t2,_)) -> do
    isCovariant <- lift $ t1 `isSubtypeOf` t2
    iop $ "covariant: " <> (show isCovariant)
    iop $ (show t1)
    iop $ (show t2)
    when (not isCovariant) $ exit (return False)
  iop "aftercovariant"

  -- when (constraints eff1 /= constraints eff2) $ exit (return False)
  iop $ "constraints eff1"
  mapM (iop . show) (constraints eff1)
  iop $ "constraints eff2"
  mapM (iop . show) (constraints eff2)
  unless (all (`elem` constraints eff1) $ constraints eff2) $ exit (return False)

  return $ return True
