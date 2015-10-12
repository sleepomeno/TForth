{-# LANGUAGE DeriveDataTypeable, DeriveFunctor, FlexibleContexts,
             FlexibleInstances, FunctionalDependencies, LambdaCase, MultiWayIf,
             NoMonomorphismRestriction, OverloadedStrings,
             RankNTypes, RecordWildCards, TemplateHaskell, TupleSections,
             TypeFamilies #-}

module TF.HasEffects.ControlStructures where
import           Control.Arrow
import Control.Applicative
import           Control.Error            as E
import Control.Monad.Error.Class (MonadError)
import           Control.Lens             hiding (noneOf, (??), _Empty)
import           Control.Monad.Error.Lens
import           Control.Monad.Extra
import           Control.Monad.Reader
import           Control.Monad.Writer
import           Control.Monad.Cont
import           Data.String
-- import           Lens.Family.Total        hiding ((&))
import           Text.PrettyPrint         (Doc, hcat, nest, render, style, text,
                                           vcat, ($+$), (<+>))
import           TF.StackCalculus
import Data.Function (on)
import           TF.StackEffectParser
import           TF.WildcardRules
import           TF.ForthTypes as FT

import           Control.Monad.State
import           Data.Functor
import           Data.List
import           Data.Maybe
import           Data.Monoid
import qualified TF.Types                 as T
import           TF.Util
import           TF.SubtypeUtil
-- import qualified TF.DataTypes as DT
-- import           Data.Data
import qualified Data.Map                 as M
import           Data.Typeable
import           Text.Parsec              hiding (token)
import qualified TF.Printer               as P
import           TF.Types                 hiding (isSubtypeOf, word)
import TF.Errors
import Debug.Trace

import TF.CheckerUtils
import TF.HasEffects.ForthWord

getStackEffects' (IfElseExpr thens elses) = do
    -- lift $ depth += 1
    checkNodes <- view _1

    (thenEff, isThenIntersect) <- lift $ withEmpty $ do
      (ForthEffect (thenEffs, isThenIntersect)) <- checkNodes thens
      flag' <- flag''
      let result = thenEffs & traverse._1.before %~ (flag':)
      return (result, isThenIntersect) 
    (elseEff, isElseIntersect) <- lift $ withEmpty $ do
      (ForthEffect (elseEffs, isElseIntersect)) <- checkNodes elses
      flag' <- flag''
      let result = elseEffs & traverse._1.before %~ (flag':)
      return (result, isElseIntersect)
    -- lift $ depth -= 1

    forbidMultiEffs <- lift $ views allowMultipleEffects not

    iop $ "\n\nCOMMON TYPE\n\n"

    maybeCommonType <- do
      guard1 <- allM (\(x1, x2) -> anyM (\(y1, y2) -> do
        res1 <- ((y1, isThenIntersect) `effectMatches'` (x1, isElseIntersect))
        -- res1 <- y1 `effectIsSubtypeOf` x1
        -- res2 <- y2 `effectIsSubtypeOf` x2
        return $ res1) thenEff) elseEff
      guard2 <- allM (\(x1, x2) -> anyM (\(y1, y2) -> do
        res1 <- ( (y1, isElseIntersect) `effectMatches'` (x1, isThenIntersect))
        -- res1 <- y1 `effectIsSubtypeOf` x1
        -- res2 <- y2 `effectIsSubtypeOf` x2
        return $ res1) elseEff) thenEff
      return $ msum [(guard guard1) >> Just thenEff, (guard guard2) >> Just elseEff] 

    iop $ "show maybecommentype: " <> (show $ isNothing maybeCommonType)
    when (isJust maybeCommonType) $ void $
       showEffs (fromJust maybeCommonType)

    when (forbidMultiEffs && isNothing maybeCommonType) $
      lift $ throwing (_TypeClashM . _IfElseExprNotStatic) ("IF_BRANCH: " <> showEffects thenEff, "ELSE_BRANCH: " <> showEffects elseEff)


    return $ withoutIntersect $ if forbidMultiEffs then (fromJust maybeCommonType) else thenEff ++ elseEff


getStackEffects' (IfExpr forthWordsOrExprs) = do
    res <- withEmpty''' $ do
      -- lift $ depth += 1
      checkNodes <- view _1
      (ForthEffect compExecEffs@(effs, _)) <- lift $ checkNodes forthWordsOrExprs
      -- lift $ depth -= 1

      forbidMultiEffs <- lift $ views allowMultipleEffects not

      let emptyIfEffect = compExecEffs == view _Wrapped emptyForthEffect

      when (forbidMultiEffs && not emptyIfEffect) $
        lift $ throwing (_TypeClashM . _IfExprNotStatic) ()

      let result = if emptyIfEffect then
                     compExecEffs
                   else
                     withoutIntersect' ((emptySt, emptySt) : effs)

      flag' <- lift flag''
      return $ ForthEffect $ result & _1.traverse._1.before %~ (flag':)

    iop "if culprits"
    -- showEffs $ res ^. _1
    
    return res

getStackEffects' (BeginUntil tokens) = do
    checkNodes <- view _1
    (ForthEffect (effects,i)) <- withEmpty' $ checkNodes tokens

    newEffects <- lift $ forM effects (\(c,e) -> do { c' <- removeLastFlag c effects; return (c',e)})
    return $ withIntersect i newEffects

    where
     removeLastFlag eff effects = (`runContT` return) $ callCC $ \ret -> do
      lift $ when (eff & view (after.to length) & (/=1)) $ throwing _BeginUntilNoFlag (showEffects effects)
      -- lift $ iopC $ "last datatype is: " <> (show $ eff ^.. after._head._1)
      lift $ unlessM (lastDatatypeIsFlag eff) $ throwing _BeginUntilNoFlag (showEffects effects)
      return $ eff & after %~ tail


     lastDatatypeIsFlag eff = fmap (has $ _Just.only True) . runMaybeT $ do
       let mLastType = eff ^? (after._head._1)
       lastType <- hoistMaybe mLastType
       lift $ lastType `isSubtypeOf` (NoReference $ PrimType flag)
