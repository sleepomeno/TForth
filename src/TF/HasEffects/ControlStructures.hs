{-# LANGUAGE  FlexibleContexts  #-}

module TF.HasEffects.ControlStructures where

import           Control.Error            as E
import           Control.Lens             hiding (noneOf, (??), _Empty)
import           Control.Monad.Error.Lens
import           Control.Monad.Extra
import           Control.Monad.Reader
import           Control.Monad.Writer
import           Control.Monad.Cont
import           TF.ForthTypes as FT

import           Data.Maybe
import           TF.Util
import           TF.SubtypeUtil
-- import qualified TF.DataTypes as DT
-- import           Data.Data
import           TF.Types                 hiding (word)
import TF.Errors

import TF.CheckerUtils
import TF.Type.StackEffect
import TF.Type.Nodes
import TF.HasEffects.HasStackEffects

getStackEffects' (IfElseExpr thens elses) = do
    checkNodes <- view _1

    -- TODO check exec effects -- must not leave anything on the stack!
    (thenEff, isThenIntersect) <- lift $ withEmpty $ do
      (ForthEffect (thenEffs, isThenIntersect)) <- checkNodes thens
      flag' <- flag''
      let result = thenEffs & traverse._1._before %~ (flag':)
      return (result, isThenIntersect) 
    (elseEff, isElseIntersect) <- lift $ withEmpty $ do
      (ForthEffect (elseEffs, isElseIntersect)) <- checkNodes elses
      flag' <- flag''
      let result = elseEffs & traverse._1._before %~ (flag':)
      return (result, isElseIntersect)
    -- lift $ depth -= 1

    forbidMultiEffs <- lift $ views allowMultipleEffects not

    maybeCommonType <- do
      guard1 <- allM (\(x1, x2) -> anyM (\(y1, y2) -> do
        res1 <- ((y1, isThenIntersect) `effectMatches'` (x1, isElseIntersect))
        return $ res1) thenEff) elseEff
      guard2 <- allM (\(x1, x2) -> anyM (\(y1, y2) -> do
        res1 <- ( (y1, isElseIntersect) `effectMatches'` (x1, isThenIntersect))
        return $ res1) elseEff) thenEff
      return $ msum [(guard guard1) >> Just thenEff, (guard guard2) >> Just elseEff] 


    when (forbidMultiEffs && isNothing maybeCommonType) $
      lift $ throwing (_TypeClashM . _IfElseExprNotStatic) ("IF_BRANCH: " <> showEffects thenEff, "ELSE_BRANCH: " <> showEffects elseEff)


    return $ withoutIntersect $ if forbidMultiEffs then (fromJust maybeCommonType) else thenEff ++ elseEff


getStackEffects' (IfExpr forthWordsOrExprs) = do
    res <- withEmpty''' $ do
      checkNodes <- view _1
      (ForthEffect compExecEffs@(effs, _)) <- lift $ checkNodes forthWordsOrExprs

      forbidMultiEffs <- lift $ views allowMultipleEffects not

      let emptyIfEffect = compExecEffs == view _Wrapped emptyForthEffect

      when (forbidMultiEffs && not emptyIfEffect) $
        lift $ throwing (_TypeClashM . _IfExprNotStatic) ()

      let result = if emptyIfEffect then
                     compExecEffs
                   else
                     withoutIntersect' ((emptySt, emptySt) : effs)

      flag' <- lift flag''
      return $ ForthEffect $ result & _1.traverse._1._before %~ (flag':)

    return res

getStackEffects' (BeginUntil tokens) = do
    checkNodes <- view _1
    (ForthEffect (effects,i)) <- withEmpty' $ checkNodes tokens

    newEffects <- lift $ forM effects (\(c,e) -> do { c' <- removeLastFlag c effects; return (c',e)})
    return $ withIntersect i newEffects

    where
     removeLastFlag eff effects = (`runContT` return) $ callCC $ \ret -> do
      lift $ when (eff & view (_after.to length) & (/=1)) $ throwing _BeginUntilNoFlag (showEffects effects)
      lift $ unlessM (lastDatatypeIsFlag eff) $ throwing _BeginUntilNoFlag (showEffects effects)
      return $ eff & _after %~ tail


     lastDatatypeIsFlag eff = fmap (has $ _Just.only True) . runMaybeT $ do
       let mLastType = eff ^? (_after._head._stackType)
       lastType <- hoistMaybe mLastType
       lift $ lastType `isSubtypeOf` (NoReference $ PrimType flag)
