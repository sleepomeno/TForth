{-# LANGUAGE LambdaCase, TypeFamilies,  NoMonomorphismRestriction  #-}

module TF.Util where

import Control.Monad.Identity
import Control.Monad.State
import Lens.Family.Total hiding ((&))
import Control.Monad.Writer
import Control.Lens
import           Control.Error as E
import TF.Types hiding (isSubtypeOf)
import           Text.Parsec hiding (anyToken)
import qualified Data.Text as Te
import Debug.Trace
import  Text.PrettyPrint (render,vcat, text, ($+$))
import qualified TF.Printer as P
import qualified Data.Map as M


-- fworex = iso (\case { ForthWord x -> Left x ; Expr x -> Right x }) (\case { Left x -> ForthWord x; Right x -> Expr x }) 

showClasses :: ParseState -> String
showClasses st = 
  let classesToMethods = views classInterfaces M.toList st 
      classesToFields  = views classFields M.toList st
      in
   render . vcat $ map (\((clazz, methods),(_,fields)) -> P.showClass clazz "unknown" fields methods) $ filter (\((class1, _), (class2, _)) -> class1 == class2) $ liftM2 (,) classesToMethods classesToFields

showCheckerState :: ParseState -> String
showCheckerState st = unlines [showDefinitions st, showClasses st]
showDefinitions :: ParseState -> String
showDefinitions st =
  let showColonDefinition name colonDef = render $ text name $+$ P.nested (P.colonDefinition' colonDef)
      showCreate name effs = render $ text name $+$ P.nested (vcat $ map P.stackEffectNice effs)
      keysValues = M.toList $ view definedWords' st :: [(String, Definition)]
      in
  "DICTIONARY:\n\n" ++ (unlines . map (++ "\n") . map (\(name,y) -> case y of 
                                      ColDef x -> showColonDefinition name x
                                      CreateDef x -> showCreate name x) $ keysValues)


showEffs =  mapM (iop . (\(c,e) -> render $ P.stackEffect c $+$ P.stackEffect e))
showEffs' =  mapM (iop . render . P.stackEffect)
showEff =  iop . render . P.stackEffect

iop = traceM
iopS = traceShowM


l3 = lift . lift . lift
l4 = lift . l3

logParser = False
iopP x = when logParser $ iop $ x

logChecker = True
iopC x = when logChecker $ iop $ x

logWildcardRules = True
iopW x = when logWildcardRules $ iop $ x

chosen' = fmap (^?! _Left) . runExceptT
for = flip map

blockedWith caption x = do
  iop $ "-----" ++ caption
  blocked x

blocked x = do
  iop "-----------------------"
  x
  iop "-----------------------"


emptySt :: StackEffect
emptySt = StackEffect [] [] []

emptyIntersect = Intersections False False
emptyForthEffect = ForthEffect ([(emptySt, emptySt)], emptyIntersect)

withoutIntersect effs = ForthEffect (effs, emptyIntersect)
withoutIntersect' effs = (effs, emptyIntersect)

withIntersect i effs = ForthEffect (effs, i)

asTuples = (_case & (on _Compiled (\x -> view _Wrapped x `zip` repeat emptySt))
                         & (on _Executed (\x -> zip (repeat emptySt) (view _Wrapped x))))

effsAsTuples = (_case & (on _Compiled (\x -> x `zip` repeat emptySt))
                         & (on _Executed (\x -> zip (repeat emptySt) x)))

fromThree' :: CompiledExecutedOrBoth MultiStackEffect -> [StackEffectPair]
fromThree' (One' x) = view _Wrapped x `zip` repeat emptySt
fromThree' (Two' x) = zip (repeat emptySt) (view _Wrapped x)
fromThree' (Three' (x,y)) = (x,y) & both %~ view _Wrapped & uncurry zip

-- compExecIso :: Simple Iso  (CompiledExecutedOrBoth StackEffect) CompExecEffect
-- compExecIso = iso fromThree toThree

fromThree :: CompiledExecutedOrBoth StackEffect -> StackEffectPair
fromThree (One' z) = (z, emptySt)
fromThree (Two' z) = (emptySt, z)
fromThree (Three' (z,y)) = (z,y)
          
toThree :: CompExecEffect -> CompiledExecutedOrBoth StackEffect
toThree (stE1, stE2)
  | stE1 == emptySt = Two' stE2
  | stE2 == emptySt = One' stE1
  | otherwise       = Three' (stE1, stE2)




new = review
labeled = flip label

tellExpr :: Node -> CheckerM ()
tellExpr expr = do
  d <- use depth
  lift . lift $ tell (Info [(expr, d)] [] [])


resolveRuntimeType :: [(UniqueArg, StackEffect)] -> IndexedStackType -> IndexedStackType
resolveRuntimeType resolvedRuntimes (t, i') = (setBaseType newType t, i')
  where
    newType = case baseType' t of
      NoReference t' -> NoReference $ (case t' of
        exec@(ExecutionType execToken) -> ExecutionType $ execToken & runtimeSpecified._Just %~ (\case
          UnknownR i -> (case (lookup i resolvedRuntimes) of
              Just eff -> ResolvedR i eff
              Nothing  -> UnknownR i)
          x         -> x)
        z -> z)
      y               -> y
  
updatePos pos _ (_:_) = setSourceLine (setSourceColumn pos 1) 1
updatePos pos _ [] = pos
satisfy' f = tokenPrim show updatePos (\c -> if f c then Just c else Nothing)
noneOf' cs = satisfy' (`notElem` cs)

anyToken = satisfy' (const True)


getNextParameter :: CheckerM String
getNextParameter = do
  w <- anyToken :: CheckerM Token
  return . possWordAsString $ w

possWordAsString :: Token -> String
possWordAsString = either (view name) (Te.unpack . view (parsed._Left)) 

parseUnknown :: String -> CheckerM Unknown
parseUnknown n = do
  (Left unknown) <- satisfy' (== Left (Unknown n))
  return unknown

sealed :: CheckerM x -> CheckerM x
sealed p = do
  oldState <- getState
  result <- p
  putState oldState
  return result
  

is pr = isRight . matching pr
