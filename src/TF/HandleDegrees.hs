module TF.HandleDegrees
       (  refDegree
        , setBaseType
        , baseType
        , removeDegree
         ) where

import TF.Types
import TF.Type.StackEffect


refDegree :: DataType -> Int
refDegree (Reference x) = 1 + refDegree x
refDegree (NoReference x) = 0
refDegree (Wildcard) = 0
refDegree (Dynamic) = 0
refDegree (WildcardWrapper) = 0
refDegree (UnknownType _) = 0

setBaseType :: DataType -> DataType -> DataType
setBaseType new (NoReference _) = new
setBaseType new (Reference old) = Reference $ setBaseType new old
setBaseType new _ = new 

baseType :: DataType -> DataType
baseType Dynamic = Dynamic
baseType Wildcard = Wildcard
baseType WildcardWrapper = WildcardWrapper
baseType (NoReference r) = NoReference r
baseType (Reference d) = baseType d
baseType (UnknownType i) = UnknownType i

removeDegree 0 x = x
removeDegree x (Reference y) = removeDegree (x-1) y
removeDegree x y = y
