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
    -- let nameOfDef = view (compOrExecIso.chosen._1) x
    let stEffs :: CompiledOrExecuted [StackEffect]
        -- stEffs = bimap (view _2) (view _2)  x
        stEffs = fmap snd x
        effs :: [StackEffectPair]
        effs = effsAsTuples stEffs

    -- when ((x ^. chosen._1) /= "foo") $ do
    --   iopP "FUUUUUUU"
    --   liftIO (mapM_ (putStrLn . render . (P.stackEffect) . fst) $ effs )
    return $ withoutIntersect effs

  getStackEffects (UnknownE uk) = do
    let unknownName = uk ^. _Wrapped


    -- s <- getState
    -- iop $ showCheckerState s
    -- iop " AAAAAA"
    
    throwing _UnknownWord $ "Word " <> unknownName <> " is unknown!"
    -- unexpected $ "Word " ++ unknownName ++ " is unknown!"
