module TF.HasEffects.HasStackEffects where

import           TF.Types                 hiding (isSubtypeOf, word)
import TF.Type.Nodes
import TF.Util
import TF.Errors
import Control.Lens (_Wrapped, _2)
import TF.CheckerUtils
import TF.SubtypeUtil
import TF.Type.Nodes
import TF.Type.StackEffect
import           Text.Parsec              hiding (token)
import           Control.Monad.Error.Lens
import Lens.Simple hiding (_2)
import qualified TF.Printer               as P
import           Control.Monad.Reader


type CheckerM' = ReaderT (CheckNodesT, CheckEffectsT, CollectEffectsT) CheckerM
type CheckNodesT = ([Node] -> CheckerM ForthEffect)
type CheckEffectsT = ForthEffect -> ReaderT CheckEffectsConfig CheckerM ()
type CollectEffectsT = Node -> CheckerM ()

effectMatches :: StackEffect -> StackEffect -> CheckerM' Bool
effectMatches eff1 eff2 = handling _TypeClash (const $ return False) $ withEmpty''' $ do
  let before' = StackEffect [] [] (eff1 ^. _before)
      after' = StackEffect (eff1 ^. _after) [] []
  checkEffects' <- asks (view _2) :: CheckerM' CheckEffectsT
  lift $ (`runReaderT` def) $ do
    checkEffects' $ withoutIntersect [(before', StackEffect [] [] [])]
    checkEffects' $ withoutIntersect [(eff2, StackEffect [] [] [])]
    checkEffects' $ withoutIntersect [(after', StackEffect [] [] [])]
  s <- lift getState
  let eff = map fst (s ^. _effects._Wrapped._1)
  iop "Das sind die effekte:"
  iop $ show eff



  iop " eff1"
  -- showEffs' [eff1]
  iop $ "constraints eff1"

  mapM (iop . show) (constraints eff1)
  iop $ "constraints eff2"
  mapM (iop . show) (constraints eff2)
  return $ (all (`elem` constraints eff2) $ constraints eff1) &&  ((==0) . length . filter (not . (\eff -> eff ^. _before == [] && eff ^. _after == [])) $ eff)

effectMatches' :: (StackEffect, Intersections) -> (StackEffect, Intersections) -> CheckerM' Bool
-- effectMatches' (eff1, int1) (eff2, int2)  = handling _TypeClash (const $ return False) $ withEmpty' $ do
effectMatches' (eff1, int1) (eff2, int2) = handling _TypeClash (const $ return False) $ withEmpty''' $ do
-- effectMatches' (eff1, int1) (eff2, int2) = withEmpty' $ do
-- effectMatches' (eff1, int1) (eff2, int2)  = _hand $ withEmpty' $ do
  let before' = StackEffect [] [] (eff1 ^. _before)
      after' = StackEffect (eff1 ^. _after) [] []
  checkEffects <- asks (view _2 )
  lift $ (`runReaderT` def) $ do
    checkEffects $ withIntersect int1 [(before', StackEffect [] [] [])]
    checkEffects $ withIntersect int2 [(eff2, StackEffect [] [] [])]
    checkEffects $ withIntersect int1 [(after', StackEffect [] [] [])]
  s <-  lift getState
  let eff = map fst (s ^. _effects._Wrapped._1)
  -- iop "Das sind die effekte:"
  -- iop $ show eff



  -- iop " eff1"
  -- showEffs' [eff1]
  -- iop $ "constraints eff1"

  -- mapM (iop . show) (constraints eff1)
  -- iop $ "constraints eff2"
  -- mapM (iop . show) (constraints eff2)

  
  return $ (all (`elem` constraints eff2) $ constraints eff1) &&  ((==0) . length . filter (not . (\eff -> eff ^. _before == [] && eff ^. _after == [])) $ eff)

class HasStackEffects a where
  getStackEffects :: a -> CheckerM' ForthEffect

