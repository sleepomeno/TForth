module TF.HasEffects.ForthWord where

import Control.Lens
import           Control.Monad.Error.Lens
import           Control.Monad.Writer
import           TF.Util
import           TF.Types                 hiding (isSubtypeOf, word)
import TF.Errors

import TF.HasEffects.HasStackEffects
import TF.Type.StackEffect
import TF.Type.Nodes

instance HasStackEffects ForthWord where
  getStackEffects (KnownWord pw)  = do
    -- pw ^. stacksEffects & adjustEffectsState
    let compExecEffect :: [StackEffectPair]
        compExecEffect = pw ^. _stacksEffects.to fromThree'
    -- return $ zipWith3 StackEffect (beforeArgs dataStack pw) (repeat (streamArgsOfParsedWord pw)) (afterArgs dataStack pw)
    return $ withIntersect (pw ^. _intersectionsPW) compExecEffect


  getStackEffects (DefE x) = do
    -- let stEffs :: CompiledOrExecuted [StackEffect]
    --     stEffs = view (_2._stefwiMultiEffects._Wrapped) <$> x
    --     intersect = view (_2._stefwiIntersection) <$> x
    --     effs :: [StackEffectPair]
    --     effs = effsAsTuples stEffs
    let stEffsComp = x ^.. _Compiled._2._stefwiMultiEffects._Wrapped.traverse
        stEffsExec :: [StackEffect]
        stEffsExec = x ^.. _Executed._2._stefwiMultiEffects._Wrapped.traverse
        count = max (length stEffsComp) (length stEffsExec) :: Int
        padWithEmpty effs = take count (effs ++ repeat emptySt)
        effects = zip (padWithEmpty stEffsComp) (padWithEmpty stEffsExec)
        intersectComp = getAny $ x ^. _Compiled._2._stefwiIntersection._Wrapped._Unwrapped
        intersectExec = getAny $ x ^. _Executed._2._stefwiIntersection._Wrapped._Unwrapped
    return $ withIntersect (Intersections intersectComp intersectExec) effects

    -- return $ withIntersect intersect effs

  getStackEffects (UnknownE uk) = do
    let unknownName = uk ^. _Wrapped


    -- s <- getState
    -- iop $ showCheckerState s
    -- iop " AAAAAA"
    
    throwing _UnknownWord $ "Word " <> unknownName <> " is unknown!"
    -- unexpected $ "Word " ++ unknownName ++ " is unknown!"
