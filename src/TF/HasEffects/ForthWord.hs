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
    let compExecEffect :: [StackEffectPair]
        compExecEffect = pw ^. _stacksEffects.to fromThree'
    return $ withIntersect (pw ^. _intersectionsPW) compExecEffect


  getStackEffects (DefE x) = do
    let stEffsComp = x ^.. _Compiled._2._stefwiMultiEffects._Wrapped.traverse
        stEffsExec :: [StackEffect]
        stEffsExec = x ^.. _Executed._2._stefwiMultiEffects._Wrapped.traverse
        count = max (length stEffsComp) (length stEffsExec) :: Int
        padWithEmpty effs = take count (effs ++ repeat emptySt)
        effects = zip (padWithEmpty stEffsComp) (padWithEmpty stEffsExec)
        intersectComp = getAny $ x ^. _Compiled._2._stefwiIntersection._Wrapped._Unwrapped
        intersectExec = getAny $ x ^. _Executed._2._stefwiIntersection._Wrapped._Unwrapped
    return $ withIntersect (Intersections intersectComp intersectExec) effects

  getStackEffects (UnknownE uk) = do
    let unknownName = uk ^. _Wrapped

    throwing _UnknownWord $ "Word " <> unknownName <> " is unknown!"
