{-# LANGUAGE LambdaCase, OverloadedStrings, DeriveDataTypeable, TypeFamilies, FunctionalDependencies, RecordWildCards, FlexibleContexts, RankNTypes, TemplateHaskell,  DeriveFunctor, NoMonomorphismRestriction, FlexibleInstances #-}

module TF.Util where

import Control.Monad.Identity
import Control.Monad.State
import           Control.Monad.Cont
import Lens.Family.Total hiding ((&))
import qualified Data.Text as T
import Control.Monad.Trans.Maybe
import Control.Arrow 
import Control.Monad.Writer
import           Control.Monad.Extra
import Control.Lens
import Data.Maybe
import Data.Functor
import qualified Data.Set as S
import Data.String
import           Control.Error as E
import TF.Types hiding (isSubtypeOf)
import TF.ForthTypes
import           Text.Parsec hiding (anyToken)
import qualified Data.Text as Te
import Debug.Trace
import  Text.PrettyPrint (render,($+$))
import  Text.PrettyPrint (render,vcat, text, ($+$), nest)
import qualified TF.Printer as P
import qualified Data.Map as M



-- getCommonSupertype
--   :: [(StackEffect, StackEffect)]
--      -> [(StackEffect, StackEffect)]
--      -> Text.Parsec.Prim.ParsecT
--           [Token]
--           ParseState
--           StackEffectM
--           (Maybe [(StackEffect, StackEffect)])
-- getCommonSupertype effs1 effs2 = do
--   guard1 <- allM (\(x1, x2) -> anyM (\(y1, y2) -> do
--     res1 <- y1 `effectIsSubtypeOf` x1
--     res2 <- y2 `effectIsSubtypeOf` x2
--     return $ res1) effs1) effs2
--   guard2 <- allM (\(x1, x2) -> anyM (\(y1, y2) -> do
--     res1 <- y1 `effectIsSubtypeOf` x1
--     res2 <- y2 `effectIsSubtypeOf` x2
--     return $ res1) effs2) effs1
--   return $ msum [(guard guard1) >> Just effs1, (guard guard2) >> Just effs2]

-- getCommonSupertype' effs1 effs2 = do
--   guard1 <- allM (\x1 -> anyM (\y1 -> do
--     res1 <- y1 `effectIsSubtypeOf` x1
--     return $ res1) effs1) effs2
--   guard2 <- allM (\x1 -> anyM (\y1 -> do
--     res1 <- y1 `effectIsSubtypeOf` x1
--     return $ res1) effs2) effs1
--   return $ msum [(guard guard1) >> Just effs1, (guard guard2) >> Just effs2]

-- getCommonSupertype''
--   :: [[StackEffect]]
--      -> ParsecT
--           [Token] ParseState StackEffectM (Maybe [StackEffect])
-- getCommonSupertype'' effs = runMaybeT $ foldM (\result another -> do
--                                       sup <- lift $ getCommonSupertype' result another
--                                       hoistMaybe sup) (head effs) (tail effs)

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
      keysValues = M.toList $ view definedWords' st :: [(String, Definition')]
      in
  "DICTIONARY:\n\n" ++ (unlines . map (++ "\n") . map (\(name,y) -> case y of 
                                      Left x -> showColonDefinition name x
                                      Right x -> showCreate name x) $ keysValues)


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

emptyIntersect = IntersectionType False False
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

tellExpr :: ForthWordOrExpr -> CheckerM ()
tellExpr expr = do
  d <- use depth
  lift . lift $ tell (Info [(expr, d)] [] [])


resolveRuntimeType :: [(UniqueArg, StackEffect')] -> IndexedStackType -> IndexedStackType
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
  


-- constraints :: StackEffect -> [(Int, Int)]
-- constraints stEff =
--   [(i,i') | (i , (type1, typeIndex1)) <- typeByPosition,
--             (i', (type2, typeIndex2)) <- typeByPosition,
--              type1 == type2,
--              typeIndex1 == typeIndex2,
--              i /= i', typeIndex1 /= Nothing] 
--    where
--      consuming = stEff ^. before
--      producing = stEff ^. after
--      streamArguments = stEff ^.. streamArgs.traverse._Defining.argType._Just
--      typeByPosition :: [(Int, IndexedStackType)]
--      typeByPosition = zip [0..] (consuming ++ streamArguments ++ producing)
     
      

-- effectIsSubtypeOf :: StackEffect -> StackEffect -> CheckerM Bool
-- effectIsSubtypeOf eff1 eff2 =  (`runContT` id) $ callCC $ \exit -> do
--   let (before1, before2) = (view before *** view before) $ (eff1, eff2)
--       (after1, after2)   = (view after *** view after) $ (eff1, eff2)
--       (streamArgs1, streamArgs2)   = (view streamArgs *** view streamArgs) $ (eff1, eff2)
--       -- (allTypes1, allTypes2) = (allTypes *** allTypes) $ (eff1, eff2)
--       sameLengths = (length before1 == length before2) && (length after1 == length after2) && (length streamArgs1 == length streamArgs2) -- && (length (allTypes1 ^. _1) == length (allTypes2 ^. _1)) && (length (allTypes2 ^. _2) == length (allTypes1 ^. _2))
--       streamArgsSameKind = all (\(arg1,arg2) -> (has _NotDefining arg1 && has _NotDefining arg2) ||
--                                                 (has (_Defining.argType._Just) arg1 && has (_Defining.argType._Just) arg2) ||
--                                                 (has (_Defining.argType._Nothing) arg1 && has (_Defining.argType._Just) arg2) ||
--                                                 (has (_Defining.argType._Nothing) arg1 && has (_Defining.argType._Nothing) arg2)) $ zip streamArgs1 streamArgs2 :: Bool


--   -- iop "before argskind"
--   when (not $ sameLengths && streamArgsSameKind) $ exit (return False)
--   -- iop "after argskind"

--   forM_ (zip before1 before2) $ \((t1,_),(t2,_)) -> do
--     isContravariant <- lift $ t2 `isSubtypeOf` t1
--     iop $ "iscontravariant: " ++ show isContravariant
--     when (not isContravariant) $ exit (return False)
--   iop "FUUUU"

--   forM_ (zip after1 after2) $ \((t1,_),(t2,_)) -> do
--     isCovariant <- lift $ t1 `isSubtypeOf` t2
--     iop $ "covariant: " <> (show isCovariant)
--     iop $ (show t1)
--     iop $ (show t2)
--     when (not isCovariant) $ exit (return False)
--   iop "aftercovariant"

--   -- when (constraints eff1 /= constraints eff2) $ exit (return False)
--   iop $ "constraints eff1"
--   mapM (iop . show) (constraints eff1)
--   iop $ "constraints eff2"
--   mapM (iop . show) (constraints eff2)
--   unless (all (`elem` constraints eff1) $ constraints eff2) $ exit (return False)

--   return $ return True
      
-- isSubtypeOf :: DataType -> DataType -> CheckerM Bool
-- isSubtypeOf t1 t2 = do
--   subtypeRelationSet <- view subtypeRelation <$> getState :: CheckerM (S.Set (BasicType, BasicType))
--   if refDegree t1 == refDegree t2 then do
--     let baseType1 = baseType' t1  :: DataType
--         baseType2 = baseType' t2
--         -- bothNotWildcard = has _NoReference baseType1 && has _NoReference baseType2
--         -- subtypeOfWildcard = ((not (has _Wildcard baseType1) && has _Wildcard baseType2)) || ((not (has _WildcardWrapper baseType1) && has _WildcardWrapper baseType2)) || (has _Wildcard baseType1 && has _Wildcard baseType2) || (has _Dynamic baseType1 || has _Dynamic baseType2 || has (_NoReference._PrimType.symbol.only DYN) baseType1 || has (_NoReference._PrimType.symbol.only DYN) baseType2)
--         subtypeOfWildcard = ((not (has _Wildcard baseType1) && has _Wildcard baseType2)) || ((not (has _WildcardWrapper baseType1) && has _WildcardWrapper baseType2)) || (has _Wildcard baseType1 && has _Wildcard baseType2) || (has _Dynamic baseType1 || has _Dynamic baseType2 || has (_NoReference._PrimType.symbol.only DYN) baseType1 || has (_NoReference._PrimType.symbol.only DYN) baseType2)
--         subtypeOfXT :: Bool
--         subtypeOfXT = fromMaybe False $ do
--           r1 <- baseType1  ^? _NoReference._ExecutionType.runtimeSpecified._Just
--           r2 <- baseType2 ^? _NoReference._ExecutionType.runtimeSpecified._Just
--           r1' <- (r1 ^? _KnownR) `mplus` (r1 ^? _ResolvedR._2)
--           r2' <- (r2 ^? _KnownR) `mplus` (r2 ^? _ResolvedR._2)
--           return $ r1' == r2'
--         inSubtypeRelation = fromMaybe False $ do
--           type1 <- baseType1 ^? _NoReference
--           type2 <- baseType2 ^? _NoReference
--           return $ S.member (type1, type2) subtypeRelationSet

--     -- iop "Type 1"
--     -- let t1' = P.dataType $ ((baseType1, Nothing) :: IndexedStackType)
--     -- iop $ render t1'
--     -- iop $ "has dynamic: " ++ show (has _Dynamic baseType1)
--     -- iop "Type 2"
--     -- let t2' = P.dataType $ ((t2, Nothing) :: IndexedStackType)
--     -- iop $ render t2'

--     return $ subtypeOfXT || inSubtypeRelation || subtypeOfWildcard
--   else return False 
    

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
