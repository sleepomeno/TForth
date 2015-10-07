{-# LANGUAGE FlexibleContexts #-}
module TF.StackCalculus
       (applyRule1, applyRule2, applyRule3, applyRule4, applyRules)
       where

import Data.String
import Control.Arrow 
import           Control.Error as E
import           Control.Monad.Reader
import           Control.Lens hiding (noneOf,(??))
-- import           Control.Monad.Trans.Either (runEitherT, EitherT)
import Lens.Family.Total hiding ((&))
import           Control.Monad
import           Control.Monad.Error.Lens
import  Text.PrettyPrint (render,vcat)
import TF.WildcardRules

import           Control.Monad.State
import Data.Functor
import Data.List
import Data.Maybe
import           TF.Util

import qualified TF.Types as T hiding (isSubtypeOf)
import           TF.Types hiding (isSubtypeOf, word)
import           Text.Parsec hiding (token)
import Data.Data
import Data.Typeable
import qualified TF.Printer as P
import qualified Data.Map as M
import qualified Data.Set as S
import TF.SubtypeUtil (isSubtypeOf)

applyRule1 :: (StackEffect, StackEffect) -> MaybeT StackRuleM StackEffect
applyRule1 (stE1,stE2) = do
  -- iop $ "will 1 be applied?"
  let b = null $ stE1 ^. after -- views after null stE1
  forcedAssertion <- view isForcedAssertion

  when (b && forcedAssertion && (not . null $ stE2 ^. before)) $
    void typeClash

  assert b
   
  -- iop $ "stE1"
  -- iop $ render . P.stackEffect $ stE1
  -- iop $ "stE2"
  -- iop $ render . P.stackEffect $ stE2

  iop $ "Rule 1 will be applied"
  -- Rule 1 is applicable if @after@ of state is empty
  let beforeTypes2 = stE2 ^. before 
      toTypes2 = stE2 ^. after 
  
  return $ stE1 &~ before %= (++ beforeTypes2) &~ after .= toTypes2
           &~ streamArgs %= (++ (view streamArgs stE2)) & streamArgs %~ resolveArgs

resolveArgs :: [DefiningOrNot] -> [DefiningOrNot]
resolveArgs  = id -- filter (either (view resolved >>> isNothing) (view resolved >>> isNothing)) 

---- Rule 2 ------
applyRule2 :: (StackEffect, StackEffect) -> MaybeT StackRuleM StackEffect
applyRule2 (stE1,stE2) = do
  -- iop $ "will 2 be applied?"
  let before2 = stE2 ^. before 
      after2 = stE2 ^. after 
      after1 = stE1 ^. after 
  forcedAssertion <- view isForcedAssertion

  when (null before2 && forcedAssertion && (not . null $ after1)) $
    void typeClash

  assert $ null before2
  iop $ "Rule 2 will be applied"
  -- Rule 2 is applicable if @before@ of the word is empty
  return $ stE1 &~ after %= (after2 ++) &~ streamArgs %= (++ (view streamArgs stE2)) & streamArgs %~ resolveArgs

---- Rule 3 ------
applyRule3 :: (StackEffect, StackEffect) -> MaybeT StackRuleM StackEffect
applyRule3 (stE1, stE2) = do
    -- iop $ "will 3 be applied?"
    
    
    (topOfStack,_) <- hoistMaybe $ preview (after.traverse) stE1
    (topOfArgs,_)  <- hoistMaybe $ preview (before.traverse) stE2
    typesMatch <- lift $ lift $ lift $ topOfStack `isSubtypeOf` topOfArgs
    assert (not typesMatch)
    iop $ "Rule 3 will beapplied"
    iop $ "Top of stack: " ++ (show topOfStack)
    iop $ "Top of args: " ++ (show topOfArgs)
    -- Rule 3 is applicable if the top of stack of both effects match
    typeClash


---- Rule 4 -----
applyRule4 :: StackEffect -> StackEffect -> CheckerM (StackEffect, StackEffect)
applyRule4 stE1 stE2 = chosen' $ applyRule4' stE1 stE2
   where
     applyRule4' stE1 stE2 = do
        -- iop $ "will 4 be applied?"

        tS@(topOfStack,_) <- firstOf (after.traverse) stE1 ?? (stE1, stE2)
        tA@(topOfArgs,_)  <- firstOf (before.traverse) stE2 ?? (stE1, stE2)
        dataType' <- lift $ topOfStack `isSubtypeOf` topOfArgs
        -- dataType <- hoistEither . note (stE1, stE2) $ dataType'
        hoistEither $ (if dataType' then Right else Left) (stE1, stE2)
        -- Types match exactly
        iop $ "Rule 4 will beapplied since they are in a subtype relation:"
        iop $ render $ P.dataType tS
        iop $ render $ P.dataType tA

        hoistEither $ Left (stE1 & after %~ tail, stE2 & before %~ tail)


-- shows how a inner maybet which should be null is lifted upwards to
    -- a higher maybet moand
typeClash :: MaybeT StackRuleM StackEffect
-- typeClash = let clash :: MaybeT StackEffectM StackEffect
typeClash = do
  checkState' <- view checkState
  -- let clash :: EitherT SemState (ReaderT CheckEffectsConfig CheckerM) StackEffect
  let clash :: ExceptT SemState (ReaderT CheckEffectsConfig CheckerM) StackEffect
      clash = hoistEither (Left checkState')
  lift $  clash


assert :: Bool -> MaybeT StackRuleM ()
assert = guard


applyRules :: StackEffect -> StackEffect -> StackRuleM StackEffect
applyRules stE1 stE2 = fmap fromJust . runMaybeT . msum . map ($ (stE1,stE2)) $ [applyRule1, applyRule2, applyRule3]
