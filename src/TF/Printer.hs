{-# LANGUAGE LambdaCase #-}
module TF.Printer where

import Prelude hiding (Word)
import  Text.PrettyPrint ((<+>),($+$),text,Doc,vcat,nest,hsep,render)
import  Text.Show.Pretty (ppDoc)
import Lens.Family.Total hiding ((&))
import           TF.Types hiding (word, forthWordOrExpr)
import           Control.Lens hiding (noneOf)
import Control.Arrow ((***),(>>>))
import Data.Monoid
import Data.Maybe
import TF.Util (nodeIso, tokenIso,compOrExecIso)

import Debug.Trace
import TF.ForthTypes
import TF.Type.StackEffect
import TF.Type.Nodes

nested = nest 1

pprint :: [Node] -> Doc
pprint = vcat . map (either forthWord expr . view nodeIso) 

forthWordOrExpr = either forthWord expr . view nodeIso
infoNode = either infoForthWord infoExpr . view nodeIso


possibleWord :: Token -> Doc
possibleWord = either unknown wordSemantics . view tokenIso

possibleWords :: [Token] -> Doc
possibleWords = vcat . map (either unknown wordSemantics. view tokenIso) 

unknown :: Unknown -> Doc
unknown (Unknown name) = text "Unknown named:" <+> text name

wordSemantics :: Word -> Doc
wordSemantics w = text "Word:" <+> text (w ^. _nameW)

compiledOrExecuted :: CompiledOrExecuted MultiStackEffect -> Doc
compiledOrExecuted effs = case effs of
  Compiled effs -> showArgs "Compiled" effs
  Executed effs -> showArgs "Executed" effs

compiledOrExecutedOrBoth :: CompiledExecutedOrBoth MultiStackEffect -> Doc
compiledOrExecutedOrBoth = _case & on _CompiledEff (showArgs "Compiled")
                           & on _ExecutedEff (showArgs "Executed")
                           & on _CompAndExecutedEff (showEffs "Comp" *** showEffs "Exec" >>> uncurry ($+$)) 

-- compiledOrExecutedOrBoth :: CompiledExecutedOrBoth StackEffect -> Doc
-- compiledOrExecutedOrBoth s = s & (_case & on _CompiledEff (\x -> text "Compiled" $+$ nested (stackEffect x))
--                            & on _ExecutedEff (\x -> text "Executed" $+$ nested (stackEffect x))
--                            & on _CompAndExecutedEff (nested . stackEffect *** nested . stackEffect >>> uncurry ($+$) >>> (text "CompExecuted" $+$)) )

-- showArgs'  = \(CDR_StackEffects c d r) -> text compExec $+$ nested (vcat . map stackEffectOnlyArgs $ d )

showArgs compExec = \(MultiStackEffect d) -> text compExec $+$ nested (vcat . map stackEffectOnlyArgs $ d )
showEffs compExec = \(MultiStackEffect d) -> text compExec $+$ nested (vcat . map stackEffect $ d )


infoForthWord :: ForthWord -> Doc
infoForthWord (UnknownE (Unknown x)) = text $ "Unknown " <> x
infoForthWord (DefE def) = text "DefE" <+> (text $ def ^. compOrExecIso.chosen._1)
infoForthWord (KnownWord (ParsedWord _ n _ _ _)) = text "KnownWord" <+> (text n)
                                             
forthWord :: ForthWord -> Doc
forthWord e@(UnknownE _) = ppDoc e
forthWord e@(DefE _) = ppDoc e
forthWord (KnownWord (ParsedWord _ n s _ _)) = text "ParsedWord:" <+> ppDoc n $+$ nest 1 (compiledOrExecutedOrBoth s)

multiEffects (MultiStackEffect d) = text "Data Stack" $+$ nested (vcat . map stackEffect $ d)

stackEffectOnlyArgs(StackEffect b streamArgs a) = if (not . null $ streamArgs) then
                                                    text "StreamArgs" $+$ nested (vcat . map definingOrNot $ streamArgs) 
                                                  else
                                                    mempty

showMethods :: [(Method, OOMethodSem)] -> Doc
showMethods methods = text "METHODS" $+$ nested (vcat . map (\(methodName, oomethodsem) -> text methodName $+$ oomethod oomethodsem) $ methods )
                                                    

showFields variables = text "VARIABLES" $+$ nested (vcat . map (\(fieldName, fieldSem) -> text fieldName $+$ oofield fieldSem) $ variables)


dataTypeNice Dynamic = text "dyn"
dataTypeNice WildcardWrapper = text "wwr"
dataTypeNice Wildcard = text "x"
dataTypeNice (UnknownType id) = text $ "unknown-" <> show id
dataTypeNice (Reference x) = text "*" <+> dataTypeNice x
dataTypeNice (NoReference bType) = bTypeNice bType

bTypeNice (ClassType clazz) = text clazz
bTypeNice (PrimType (PT sym _  _ _ )) = text (show sym)
bTypeNice (ExecutionType (ExecutionToken _ runtimeSpec)) = text "xt:[" <+> case runtimeSpec of
  Nothing -> text "Nothing"
  Just runtime -> case runtime of
    NoR -> text "NoR"
    UnknownR arg -> text "UnknownR"
    KnownR eff -> stackEffectNice eff
    ResolvedR arg eff -> stackEffectNice eff
  
                       
stackEffectNice (StackEffect b args a ) = text "(" <+> (hsep $ showTypes $ reverse b) <+> (hsep $ map definingOrNot args) <+> text " -- " <+> (hsep $ showTypes $ reverse a) <+> text ")"
  where
    -- showTypes types = map (\(t,i) -> dataTypeNice t <+> (text . show $ i)) types
    showTypes types = map (\(t,i) -> dataTypeNice t) types

stackEffect(StackEffect b streamArgs a) = text "Effect" $+$
                                   nested (text "Before") $+$
                                      nest 2 (indexedArgs b) $+$
                                   nested (text "StreamArgs") $+$
                                      nest 2 (vcat . map definingOrNot $ streamArgs) $+$
                                   nested (text "After") $+$
                                      nest 2 (indexedArgs a)

stackEffectWithoutArgs(StackEffect b streamArgs a) = text "Effect" $+$
                                   nested (text "Before") $+$
                                      nest 2 (indexedArgs b) $+$
                                   nested (text "After") $+$
                                      nest 2 (indexedArgs a)

definingOrNot :: DefiningOrNot -> Doc
definingOrNot = ppDoc
definingOrNotNice :: DefiningOrNot -> Doc
definingOrNotNice (Defining arg) = text $ ":'" <> arg ^. _definingArgInfo._argName <> "'"
definingOrNotNice (NotDefining arg) = text $ "'" <> arg ^. _streamArgInfo._argName <> "'"

indexedArgs :: [IndexedStackType] -> Doc
indexedArgs indexedArgs = vcat $ map dataType (indexedArgs ^.. traverse)

oomethod :: OOMethodSem -> Doc
oomethod Empty = text "EMPTY"
oomethod (ByDefinition (effs, forced)) = text "ByDefinition" $+$ nested (effsAndForced effs forced)
oomethod (InferredByMethod (effs, forced)) = text "InferredByMethod" $+$ nested (effsAndForced effs forced)

oofield :: OOFieldSem -> Doc
oofield (ByFieldDefinition eff) = text "ByFieldDefinition" $+$ nested (stackEffect eff)
oofield (InferredByField eff) = text "InferredByField" $+$ nested (stackEffect eff)

effsAndForced :: [StackEffect] -> Bool -> Doc
effsAndForced effs forced = text ("Forced " ++ show forced) $+$ text "EFFECTS" $+$ nested (vcat (map stackEffect effs))


assertFailure :: AssertFailure -> Doc
assertFailure (AssertFailure olds news) = text "OLD EFFS" $+$ (nested . vcat $ map compExecEff olds) $+$
                                        text "NEW EFFS" $+$ (nested . vcat $ map compExecEff news)

checkFailure :: CheckFailure -> Doc
checkFailure (CheckFailure olds news) = text "OLD EFFS" $+$ (nested . vcat $ map compExecEff olds) $+$
                                        text "NEW EFFS" $+$ (nested . vcat $ map compExecEff news)

compExecEff :: CompExecEffect -> Doc
compExecEff (cEff, eEff) = text "COMP EFFECT" $+$ nested (stackEffect cEff) $+$
                            text "EXEC EFFECT" $+$ nested (stackEffect eEff)
                               

infoControlExpr :: ControlStructure -> Doc
infoControlExpr (IfExpr _) = text "IF"
infoControlExpr (IfElseExpr _ _) = text "IF_ELSE"
infoControlExpr (DoPlusLoop _) = text "DOPLUSLOOP"
infoControlExpr (DoLoop _) = text "DOLOOP"
infoControlExpr (BeginUntil _) = text "BEGIN_UNTIL"
infoControlExpr (BeginWhileRepeat _ _) = text "BEGIN_WHILE_REPEAT"

infoOOPExpr :: OOPExpr -> Doc
infoOOPExpr (NoName _ _ clazz method) = text $ "Noname for class " ++ clazz ++ " and method " ++ method
infoOOPExpr (NoNameClash _ clazz method) = text $ "NonameClash for class " ++ clazz ++ " and method " ++ method
infoOOPExpr (Class name _ _ _) = text $ "CLASS " ++ name
infoOOPExpr (NewObject _) = text "NEW OBJECT"
infoOOPExpr (FieldCall f) = text "FIELD CALL of" <+> text (f ^. compOrExecIso.chosen)

infoExpr :: Expr -> Doc
infoExpr (Create _ _ _) = text "CREATE"
infoExpr (Assert _ _) = text "ASSERT"
infoExpr (Cast _) = text "CAST"
infoExpr (Interpreted _) = text "INTERPRETED"
infoExpr (ColonExpr n _ _) =  text $ "COLONEXPR " ++ n
infoExpr (ColonExprClash n w) = text $ "COLONCLASH " ++ n
infoExpr (ColonExprImmediate n _ _) = text $ "COLON_IMMEDIATE " ++ n
infoExpr (Postpone _) = text "Postpone"
infoExpr (Tick eff pw) = text "TICK"
infoExpr (Execute _) = text "EXECUTE"
infoExpr (Include _) = text "INCLUDE"
infoExpr (Require _) = text "REQUIRE"
infoExpr (ControlExpr x) = infoControlExpr x
                            
controlStructure :: ControlStructure -> Doc
controlStructure (IfExpr xs) = text "IF" $+$ nested (pprint xs)
controlStructure (IfElseExpr ifs elses) = text "IF" $+$ nested (pprint ifs) $+$ text "ELSE" $+$ nested (pprint elses)
controlStructure (DoPlusLoop xs) = text "DO" $+$ nested (pprint xs) $+$ text "+LOOP"
controlStructure (DoLoop xs) = text "DO" $+$ nested (pprint xs) $+$ text "LOOP"
controlStructure (BeginUntil xs) = text "BEGIN" $+$ nested (pprint xs) $+$ text "UNTIL"
controlStructure (BeginWhileRepeat xs ys) = text "BEGIN" $+$ nested (pprint xs) $+$ text "WHILE" $+$ nested (pprint ys) $+$ text "REPEAT"

oopExpr :: OOPExpr -> Doc
oopExpr (NoName sem _ clazz method) = text "NONAME" $+$ nested (text (clazz ++ "." ++ method) $+$ nested (fromMaybe mempty (fmap ((((text "Comment:") $+$) . nested) . uncurry effsAndForced) sem)))
oopExpr (NoNameClash _ clazz method) = text "NONAME_CLASH" $+$ (nested $ text $ clazz ++ "." ++ method)
oopExpr (Class name variables methods oldClass) = showClass name oldClass variables methods
oopExpr (NewObject compOrExec) = text "NEW OBJECT" <+> text "which is" <+> typeOfObject
                              where
                                typeOfObject = case compOrExec of
                                  Compiled x -> text "compiled of class" <+> text x
                                  Executed x -> text "executed of class" <+> text x
oopExpr (FieldCall cOre) = text "FIELD CALL of" <+> text (cOre ^. compOrExecIso.chosen) <+> text "which is" <+> text (either (const "compiled") (const "executed") . view compOrExecIso $ cOre)
                           
expr :: Expr -> Doc
expr (OOPExpr x) = oopExpr x
expr (ControlExpr x) = controlStructure x
expr (Create create initialization does) = text "CREATE" $+$ printInit initialization  $+$ printDoes does
   where
     printInit Nothing = mempty
     printInit (Just (exprs, comma)) = nested (text "INIT" $+$ nested (pprint exprs $+$  forthWordOrExpr comma))
     printDoes Nothing = mempty
     printDoes (Just exprs) = nested (text "DOES" $+$ nested (pprint exprs))
expr (Assert xs f) = text "Assert" $+$ compiledOrExecuted (xs & compOrExecIso.chosen %~ MultiStackEffect)
expr (Cast xs ) = text "Cast" $+$ compiledOrExecuted (xs & compOrExecIso.chosen %~ MultiStackEffect)
expr (Interpreted xs) = text "INTERPRETED" $+$ nested (pprint xs)
expr (ColonExpr n sem xs) = text "COLON" <+> text n $+$ nested (ppDoc sem) $+$ nested (pprint xs)
expr (ColonExprClash n sem) = text "COLONCLASH" <+> text n $+$ nested (ppDoc sem)
expr (ColonExprImmediate n sem xs) = text "COLON-IMMEDIATE" <+> text n $+$ nested (ppDoc sem) $+$ nested (pprint xs)

-- expr (Postpone x) = text "Postpone" $+$ nested (either text (text . view name) x)
expr (Postpone x) = text "Postpone" $+$ nested ((either text text) x)

expr (PostponeImmediate x) = text "PostponeImmediate" $+$ nested (forthWord x)
expr (Tick effects pw) =  text "TICK" $+$ nested ((text "EFFECTS:" $+$ nested (vcat $ map stackEffect effects)) $+$ (text "PARSED_WORD:" $+$ nested (forthWord (KnownWord pw))))
expr (Execute xs) = text "Execute" $+$ compiledOrExecuted (xs & compOrExecIso.chosen %~ MultiStackEffect)
expr (Include file) = text $ "Include: " <> file
expr (Require file) = text $ "Require: " <> file
                                                                                                 

showClass clazz oldClass fields methods = text ("CLASS " ++ clazz ++ ", derived from " ++ oldClass) $+$ nested ((showFields fields) $+$ showMethods methods)


dataType (UnknownType identifier, index) = text $ "UnknownType with identifier " ++ show identifier ++ " and index " ++ show index
dataType (Dynamic, index) = text $ "Dynamic with Index " ++ show index
dataType (Wildcard, index) = text $ "Wildcard with Index " ++ show index
dataType (WildcardWrapper, index) = text $ "WildcardWrapper with Index " ++ show index
dataType (Reference x, index) = text "Reference" $+$ nested (dataType (x, index))
dataType (NoReference basicType, index) = case basicType of 
  PrimType (PT sym _ _ asString) ->  text "PrimType" <+> text (show sym) <+> text ", as string:" <+> text asString <+> text (", Index is " ++ show index)
  ClassType className -> text ("ClassType " ++ className) <+> text (", Index is " ++ show index)
  ExecutionType token -> text "ExecutionType" $+$ nested (ppDoc token) 


multiStackEffect (MultiStackEffect effs) = vcat $ map stackEffect effs

colonDefinition' :: ColonDefinitionProcessed -> Doc
colonDefinition' (ColonDefinitionProcessed c effsByPhase) = (case effsByPhase of
                                                  Checked (StackEffectsWI effs (Intersection intersect)) -> (text ("Stack effect inferred: (" <> (if intersect then "" else "NOT ") <> " INTERSECT)")) $+$ (nested . multiStackEffect $ effs)
                                                  NotChecked -> text "Stack effect not Checked"
                                                  Forced (StackEffectsWI effs _) -> text "Stack effect forced" $+$ (nested . multiStackEffect $ effs)
                                                  Failed s -> text ("FAILURE: " ++ s))

colonDefinition'' :: ColonDefinition -> Doc
colonDefinition'' (ColonDefinition _ (ColonDefinitionMeta n _)) = text ("COLON_DEFINTION " ++ n)


realtype :: PrimType -> Doc
realtype (PT x _ _ _ ) = text (show x)

