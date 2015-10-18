{-# LANGUAGE  TemplateHaskell, FunctionalDependencies, FlexibleInstances, DeriveDataTypeable #-}

module TF.ForthTypes where

import  Control.Lens
import           Data.Data hiding (DataType)


data Size = One | Two | ImpDependent | ZeroOrMore deriving (Show,Read,Eq,Data,Typeable, Ord)
data TypeSymbol = Flag | STrue | SFalse | Char | N | Plus_N | U | NU | X | XT | ADDR | AADDR | CADDR | D | PLUS_D | UD | DUD | XD | DYN deriving (Show,Read,Eq,Data,Ord,Typeable, Enum)

data PrimType = PT { _pSymbol :: TypeSymbol
                  , _pDescription :: String
                  , _pSize :: Size
                  , _pAsString :: String
                  } deriving (Show,Eq,Ord)
makeLensesWith abbreviatedFields ''PrimType
-- makeFields ''PrimType

flag = PT Flag "flag" One "flag"
true = PT STrue "true flag" One "true"
false = PT SFalse "false flag" One "false"
char = PT Char "character" One "char"
n :: PrimType
n = PT N "signed number" One "n"
plusN = PT Plus_N "non-negative number" One "+n"
u = PT U "unsigned number" One "u"
-- nu = PT NU "number" One
x = PT X "unspecified cell" One "x"
dyn = PT DYN "unspecified cell" One "dyn"
-- xt = PT XT "execution token" One "xt"
addr = PT ADDR "address" One "addr"
aaddr = PT AADDR "aligned address" One "a-addr"
caddr = PT CADDR "character-aligned address" One "c-addr"
d = PT D "double-cell signed number" Two "d"
plusD = PT PLUS_D "double-cell non-negative number" Two "+d"
ud = PT UD "double-cell unsigned number" Two "ud"
-- dud = PT DUD "double-cell number" Two
xd = PT XD "unspecified cell pair" Two "xd"

forthTypes :: [PrimType]
forthTypes = [flag, true, false, char, plusN, u,
         addr, aaddr, caddr, d, plusD, xd, -- TODO 
         ud, x, n]

