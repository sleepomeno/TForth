{-# LANGUAGE FlexibleContexts #-}

module TF.StackCalculus
       (applyRule1, applyRule2, applyRule3, applyRule4, applyRules)
       where

import           Control.Error as E
import           Control.Monad.Reader
import           Control.Lens hiding (noneOf,(??))
-- import           Control.Monad.Trans.Either (runEitherT, EitherT)
import  Text.PrettyPrint (render)

import Data.Maybe
import           TF.Util

import           TF.Types hiding (isSubtypeOf, word)
import qualified TF.Printer as P
import TF.SubtypeUtil (isSubtypeOf)
import TF.Type.StackEffect
import TF.Type.Nodes

applyRule1 :: (StackEffect, StackEffect) -> MaybeT StackRuleM StackEffect
applyRule1 (stE1,stE2) = do
  -- iop $ "will 1 be applied?"
  let b = null $ stE1 ^. _after -- views after null stE1
  forcedAssertion <- view isForcedAssertion

  when (b && forcedAssertion && (not . null $ stE2 ^. _before)) $
    void typeClash

  assert b
   
  -- iop $ "stE1"
  -- iop $ render . P.stackEffect $ stE1
  -- iop $ "stE2"
  -- iop $ render . P.stackEffect $ stE2

  -- Rule 1 is applicable if @after@ of state is empty
  let beforeTypes2 = stE2 ^. _before 
      toTypes2 = stE2 ^. _after 
  
  return $ stE1 &~ _before %= (++ beforeTypes2) &~ _after .= toTypes2
           &~ _streamArgs %= (++ view _streamArgs stE2) & _streamArgs %~ resolveArgs

resolveArgs :: [DefiningOrNot] -> [DefiningOrNot]
resolveArgs  = id -- filter (either (view resolved >>> isNothing) (view resolved >>> isNothing)) 

---- Rule 2 ------
applyRule2 :: (StackEffect, StackEffect) -> MaybeT StackRuleM StackEffect
applyRule2 (stE1,stE2) = do
  -- iop $ "will 2 be applied?"
  let before2 = stE2 ^. _before 
      after2 = stE2 ^. _after 
      after1 = stE1 ^. _after 
  forcedAssertion <- view isForcedAssertion

  when (null before2 && forcedAssertion && (not . null $ after1)) $
    void typeClash

  assert $ null before2
  -- Rule 2 is applicable if @before@ of the word is empty
  return $ stE1 &~ _after %= (after2 ++) &~ _streamArgs %= (++ view _streamArgs stE2) & _streamArgs %~ resolveArgs

---- Rule 3 ------
applyRule3 :: (StackEffect, StackEffect) -> MaybeT StackRuleM StackEffect
applyRule3 (stE1, stE2) = do
    -- iop $ "will 3 be applied?"
    
    
    (topOfStack,_) <- hoistMaybe $ preview (_after.traverse) stE1
    (topOfArgs,_)  <- hoistMaybe $ preview (_before.traverse) stE2
    typesMatch <- lift $ lift $ lift $ topOfStack `isSubtypeOf` topOfArgs
    assert (not typesMatch)
    -- Rule 3 is applicable if the top of stack of both effects match
    typeClash


---- Rule 4 -----
applyRule4 :: StackEffect -> StackEffect -> CheckerM (StackEffect, StackEffect)
applyRule4 stE1 stE2 = chosen' $ applyRule4' stE1 stE2
   where
     applyRule4' stE1 stE2 = do
        -- iop $ "will 4 be applied?"

        tS@(topOfStack,_) <- firstOf (_after.traverse) stE1 ?? (stE1, stE2)
        tA@(topOfArgs,_)  <- firstOf (_before.traverse) stE2 ?? (stE1, stE2)
        dataType' <- lift $ topOfStack `isSubtypeOf` topOfArgs
        -- dataType <- hoistEither . note (stE1, stE2) $ dataType'
        hoistEither $ (if dataType' then Right else Left) (stE1, stE2)
        -- Types match exactly

        hoistEither $ Left (stE1 & _after %~ tail, stE2 & _before %~ tail)


-- shows how a inner maybet which should be null is lifted upwards to
    -- a higher maybet moand
typeClash :: MaybeT StackRuleM StackEffect
typeClash = do
  checkState' <- view checkState
  let clash :: ExceptT SemState (ReaderT CheckEffectsConfig CheckerM) StackEffect
      clash = hoistEither (Left checkState')
  lift  clash


assert :: Bool -> MaybeT StackRuleM ()
assert = guard


applyRules :: StackEffect -> StackEffect -> StackRuleM StackEffect
applyRules stE1 stE2 = fmap fromJust . runMaybeT . msum . map ($ (stE1,stE2)) $ [applyRule1, applyRule2, applyRule3]
