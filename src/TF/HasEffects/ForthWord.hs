module TF.HasEffects.ForthWord where

import Control.Lens
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
import TF.HasEffects.HasStackEffects

instance HasStackEffects ForthWord where
  getStackEffects (KnownWord pw)  = do
    -- pw ^. stacksEffects & adjustEffectsState
    let compExecEffect :: [StackEffectPair]
        compExecEffect = pw ^. stacksEffects.to fromThree'
    -- return $ zipWith3 StackEffect (beforeArgs dataStack pw) (repeat (streamArgsOfParsedWord pw)) (afterArgs dataStack pw)
    return $ withIntersect (pw ^. intersectionType) compExecEffect


  getStackEffects (DefE x) = do
    let nameOfDef = view (chosen._1) x
    let stEffs :: CompiledOrExecuted [StackEffect]
        stEffs = bimap (view _2) (view _2) x
        effs :: [StackEffectPair]
        effs = effsAsTuples stEffs

    -- when ((x ^. chosen._1) /= "foo") $ do
    --   iopP "FUUUUUUU"
    --   liftIO (mapM_ (putStrLn . render . (P.stackEffect) . fst) $ effs )
    return $ withoutIntersect effs

  getStackEffects (UnknownE uk) = do
    let unknownName = view name uk


    -- s <- getState
    -- iop $ showCheckerState s
    -- iop " AAAAAA"
    
    throwing _UnknownWord $ "Word " <> unknownName <> " is unknown!"
    -- unexpected $ "Word " ++ unknownName ++ " is unknown!"
