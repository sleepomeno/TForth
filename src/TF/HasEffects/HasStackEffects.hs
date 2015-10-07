module TF.HasEffects.HasStackEffects where

import           TF.Types                 hiding (isSubtypeOf, word)

class HasStackEffects a where
  getStackEffects :: a -> CheckerM' ForthEffect

