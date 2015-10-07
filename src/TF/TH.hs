module TF.TH where


import qualified Control.Lens.TH as TH

makeFields = TH.makeLensesWith TH.abbreviatedFields 
