module TF.TH where


import qualified Control.Lens.TH as TH
import qualified Lens.Simple as L

makeFields = TH.makeLensesWith TH.abbreviatedFields 

nameTransformation :: String -> Maybe String
nameTransformation name = Just $ '_':name

makeLens = L.makeLensesBy nameTransformation
