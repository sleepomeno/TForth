module TF.Subtypes
       (  getDefaultSubtypes
        , subtypeRelation'
        , primitiveTypes
        , isSubtypeOf ) where

import TF.Types
import Data.Tree
import           TF.ForthTypes as FT
import qualified Data.Set as S
import  Control.Lens ((^?!), dimap)
import TF.Errors


-- printSubtypes = putStrLn . drawForest $ fmap (fmap (render . P.realtype)) (subtypeForest forthTypes getSubtypes)
  
subtypeForest :: [BasicType] -> (BasicType -> [BasicType]) -> Forest BasicType
subtypeForest forthTypes' getSubTypes' = unfoldForest getSubTypesOf forthTypes'
   where
     getSubTypesOf :: BasicType -> (BasicType, [BasicType])
     getSubTypesOf supertype = (supertype, getSubTypes' supertype)

getDefaultSubtypes :: PrimType -> [PrimType]
getDefaultSubtypes (PT U _ _ _) = [plusN, addr]
getDefaultSubtypes (PT ADDR _ _ _)  = [caddr]
getDefaultSubtypes (PT CADDR _ _ _)  = [aaddr]
getDefaultSubtypes (PT Plus_N _ _ _)  = [char]
getDefaultSubtypes (PT N _ _ _)  = [plusN]
getDefaultSubtypes _ = []

subtypeRelation' :: [BasicType] -> (PrimType -> [PrimType]) -> S.Set (BasicType, BasicType)
subtypeRelation' forthTypes' getSubTypes' = S.fromList [(t1, t2) | t1 <- forthTypes',
                                            t2 <- forthTypes',
                                            let forest = subtypeForest forthTypes' (dimap (^?! _PrimType) (map PrimType) getSubTypes'),
                                            isSubtypeOf t1 t2 forest]

defaultSubtypeRelation :: S.Set (BasicType, BasicType)
defaultSubtypeRelation = subtypeRelation' primitiveTypes  getDefaultSubtypes

primitiveTypes = map PrimType forthTypes

isSubtypeOf :: BasicType -> BasicType -> Forest BasicType -> Bool

isSubtypeOf t1 t2 forest | t1 == t2  = True
isSubtypeOf t1 t2 forest = any isSubTypeOf' $ forest
  where
    isSubTypeOf' tree 
        | rootLabel tree == t2   = not . null $ concatMap (filter (== t1) . depth') (subForest tree)
        | rootLabel tree /= t2   = False

depth' :: Tree a -> [a]
depth' (Node x []) = [x]
depth' (Node x ts) = x : concatMap depth' ts
