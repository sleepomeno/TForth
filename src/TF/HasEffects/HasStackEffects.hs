module TF.HasEffects.HasStackEffects (
    effectMatches'
  , effectMatches
  , HasStackEffects
  , getStackEffects

  ) where

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
  lift $ (`runReaderT` def) $ local (tellErrors .~ False) $ do
    checkEffects' $ withoutIntersect [(before', StackEffect [] [] [])]
    checkEffects' $ withoutIntersect [(eff2, StackEffect [] [] [])]
    checkEffects' $ withoutIntersect [(after', StackEffect [] [] [])]
  s <- lift getState
  let eff = map fst (s ^. _effects._Wrapped._1)

  iopE "Effects to match:"
  iopE  "constraints eff1"
  mapM_ (iopE . show) (constraints eff1)
  iopE "constraints eff2"
  mapM_ (iopE . show) (constraints eff2)

  return $ (all (`elem` constraints eff2) $ constraints eff1) &&  ((==0) . length . filter (not . (\eff -> eff ^. _before == [] && eff ^. _after == [])) $ eff)

effectMatches' :: (StackEffect, Intersections) -> (StackEffect, Intersections) -> CheckerM' Bool
effectMatches' (eff1, int1) (eff2, int2) = handling _TypeClash (const $ return False) $ withEmpty''' $ do
  let before' = StackEffect [] [] (eff1 ^. _before)
      after' = StackEffect (eff1 ^. _after) [] []
  checkEffects <- asks (view _2 )
  lift $ (`runReaderT` def) $ local (tellErrors .~ False) $ do
    checkEffects $ withIntersect int1 [(before', StackEffect [] [] [])]
    checkEffects $ withIntersect int2 [(eff2, StackEffect [] [] [])]
    checkEffects $ withIntersect int1 [(after', StackEffect [] [] [])]
  s <-  lift getState
  let eff = map fst (s ^. _effects._Wrapped._1)

  
  return $ (all (`elem` constraints eff2) $ constraints eff1) &&  ((==0) . length . filter (not . (\eff -> eff ^. _before == [] && eff ^. _after == [])) $ eff)

class HasStackEffects a where
  getStackEffects :: a -> CheckerM' ForthEffect

