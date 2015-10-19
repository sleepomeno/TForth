{-# LANGUAGE NoMonomorphismRestriction  #-}

module TF.CheckerUtils where

import           Control.Error            as E
import           Control.Lens             hiding (noneOf, (??), _Empty)
import           Control.Monad.Error.Lens
import           Control.Monad.Extra
import           Control.Monad.Reader
import           Control.Monad.Writer
import  Text.PrettyPrint (render,vcat, text, ($+$))
import           TF.ForthTypes as FT

import           Data.List
import           TF.Util
-- import qualified TF.DataTypes as DT
import qualified Data.Map                 as M
import           Text.Parsec              hiding (token)
import qualified TF.Printer               as P
import           TF.Types                 hiding (isSubtypeOf, word)
import TF.HandleDegrees
import TF.Errors
import TF.SubtypeUtil 
import TF.Type.StackEffect
import TF.Type.Nodes

  
forceBeforesEmpty effs = forceEmpty _before effs "Before"
forceAftersEmpty effs = forceEmpty _after effs "After"

forceEmpty l effs lName colonName = do
  let allEmpty :: Bool
      allEmpty = all (null . view l) effs

  unless allEmpty $
    liftUp . throwing _UnemptyStack $ (colonName, lName ++ " of stack effects must be empty!")

withEmpty' :: CheckerM a -> ReaderT s CheckerM a
withEmpty' x  = do
  saveState <- lift getState
  let oldEffects = saveState ^. _effects
  lift $ modifyState $ _effects .~ emptyForthEffect
  parsed <- lift x
  lift $ modifyState $ _effects .~ oldEffects

  return parsed

withEmpty'''
  :: (MonadTrans t, Monad (t (ParsecT s ParseState m)), Monad m) =>
     t (ParsecT s ParseState m) b -> t (ParsecT s ParseState m) b
withEmpty''' x  = do
  saveState <- lift getState
  let oldEffects = saveState ^. _effects
  lift $ modifyState $ _effects .~ emptyForthEffect
  parsed <- x
  lift $ modifyState $ _effects .~ oldEffects

  return parsed


-- withEmpty :: CheckerM' a -> CheckerM' a
withEmpty x  = do
  saveState <- getState
  let oldEffects = saveState ^. _effects
  modifyState $ _effects .~ emptyForthEffect
  parsed <- x
  modifyState $ _effects .~ oldEffects

  return parsed

execEff :: StackEffect -> CompExecEffect
execEff s = (emptySt, s)

compEff :: StackEffect -> CompExecEffect
compEff s = (s, emptySt)

exportColonDefinition isForced colonName effs' compI = do 
    let modifier x = if isForced then
                       Forced $ StackEffectsWI x (Intersection False)
                     else
                       Checked $ StackEffectsWI x (Intersection compI) 
    forbidMulti <- views allowMultipleEffects not
    let effs = nub effs'
    checkResult <- if (length effs > 1 && forbidMulti) then do
                     iop $ "THESE ARE THE MULTI EFFS"
                     -- showEffs' effs
                     maybeCommon <- getCommonSupertype'' (map (:[]) effs)
                     case maybeCommon of
                       Just effs -> return $ modifier effs
                       Nothing   -> do
                         if compI then
                           return $ modifier effs
                         else do 
                            let message = "Multiple Effects for colon definition " <> colonName
                            unlessM (view allowLocalFailure) $ throwing (_TypeClashM._MultiEffs) message
                            return . Failed $ message
                   else
                     return $ modifier effs

    modifyState $ _definedWords'.ix colonName._ColonDefinition.processedEffects .~ checkResult
            

changeEffectsOfState :: (StackEffect -> StackEffect) -> CheckerM ()
changeEffectsOfState f = do
  s <- getState
  let comp = view _currentCompiling s

      (effs'', i) = view (_effects._Wrapped) s
      effs' = unzip effs''

  newEffs <- if comp then
               return (map f $ effs' ^. _1, effs' ^. _2)
             else
               return (effs' ^. _1, map f $ effs' ^. _2)
  modifyState $ _effects._Wrapped .~ (uncurry zip newEffs, i)
  

effectsOfState :: CheckerM [StackEffect]
effectsOfState = do
  s <- getState
  -- let comp = views stateVar (== COMPILESTATE) s
  let comp = view _currentCompiling s
      (effs'', _) = view (_effects._Wrapped) s
      effs = unzip effs''
  if comp then
    return $ effs ^. _1
  else
    return $ effs ^. _2


replaceWrappers :: [StackEffect] -> CheckerM [StackEffect]
replaceWrappers result = do 
  let wwrappersOfEff :: StackEffect -> [Int]
      wwrappersOfEff eff = toListOf (_before.wrapperLens._2._Just) eff ++ toListOf (_after.wrapperLens._2._Just) eff

      wrapperLens = traverse.filtered (\(t,_) -> baseType t == WildcardWrapper)
  let wrapperIndices = concatMap wwrappersOfEff result

  replacements <- forM (nub wrapperIndices) $ \i -> do
    uniqueId <- _identifier <<+= 1
    return (i, uniqueId)

  let changeWrappersToUnknown :: StackEffect -> StackEffect
      changeWrappersToUnknown eff = eff & _before.wrapperLens %~ replaceWrapper & _after.wrapperLens %~ replaceWrapper
      replaceWrapper (_, Nothing) = error "index of wildcardwrapper is always a just!"
      replaceWrapper (t, Just i) =
        let id = lookup i replacements
            id' = case id of
                Nothing -> error "replacement error"
                Just id'' -> id''
        in
            (setBaseType (UnknownType id') t, Just i)

  return $ map changeWrappersToUnknown result
                                  

allFieldImplementations :: Variable -> CheckerM [(ClassName, [StackEffect]) ]
allFieldImplementations field = do
  keysValues <- views _classFields M.toList <$> getState
  let filterMethods (className, fields) = do
        let fields' = filter (\(m, _) -> m == field) fields
        let effs = concatMap (\(_, oofieldsem) -> case oofieldsem of
                                                      ByFieldDefinition effs -> [effs]
                                                      InferredByField   effs -> [effs]) fields' :: [StackEffect]
        return (className, effs)

  filtered <- mapM filterMethods  keysValues -- :: CheckerM [(ClassName, [StackEffect]) ]

  return filtered

allMethodImplementationss :: Method -> CheckerM [(ClassName, [StackEffect]) ]
allMethodImplementationss method = do
  keysValues <- views _classInterfaces M.toList <$> getState
  let filterMethods (className, methods) = do
        let methods' = filter (\(m, _) -> m == method) methods
        mapM_ (\(m, oomethodsem) -> when (has _Empty oomethodsem) $
                                       throwing _Impossible "Method should have been implemented") methods'
        let effs = concatMap (\(m, oomethodsem) -> case oomethodsem of
                                                      ByDefinition (effs, _) -> effs
                                                      InferredByMethod (effs, _) -> effs) methods' :: [StackEffect]
        return (className, effs)

  mapM filterMethods  keysValues -- :: CheckerM [(ClassName, [StackEffect]) ]


noDoubleDefinition method definedEffByClass' stackCommentEffects =
  runMaybeT $ do
    definedEffByClass <- hoistMaybe definedEffByClass'
    definedEffByMethod <- hoistMaybe stackCommentEffects
    lift $ throwing _DefinedTwice ("Effect of method " ++ method ++ " has already been defined in class definition")

getEffOfMethod :: ClassName -> Method -> CheckerM (Maybe ([StackEffect], Bool))
getEffOfMethod clazz method = do
  s <- getState
  return $ preview (_classInterfaces.at clazz._Just.traverse.filtered (\(x,_) -> x == method)._2._ByDefinition) s


flag'' = do
  id <- _identifier <<+= 1
  return $ (NoReference $ PrimType FT.flag, Just id)

-- effectMatches' :: (StackEffect, Intersections) -> (StackEffect, Intersections) -> CheckerM' Bool
-- -- effectMatches' (eff1, int1) (eff2, int2)  = handling _TypeClash (const $ return False) $ withEmpty' $ do
-- effectMatches' (eff1, int1) (eff2, int2) = handling _TypeClash (const $ return False) $ withEmpty''' $ do
-- -- effectMatches' (eff1, int1) (eff2, int2) = withEmpty' $ do
-- -- effectMatches' (eff1, int1) (eff2, int2)  = _hand $ withEmpty' $ do
--   let before' = StackEffect [] [] (eff1 ^. _before)
--       after' = StackEffect (eff1 ^. _after) [] []
--   checkEffects <- view _2 
--   lift $ (`runReaderT` defCheckEffectsConfig) $ do
--     checkEffects $ withIntersect int1 [(before', StackEffect [] [] [])]
--     checkEffects $ withIntersect int2 [(eff2, StackEffect [] [] [])]
--     checkEffects $ withIntersect int1 [(after', StackEffect [] [] [])]
--   s <-  lift getState
--   let eff = map fst (s ^. _effects._Wrapped._1)
--   -- iop "Das sind die effekte:"
--   -- iop $ show eff



--   -- iop " eff1"
--   -- showEffs' [eff1]
--   -- iop $ "constraints eff1"

--   -- mapM (iop . show) (constraints eff1)
--   -- iop $ "constraints eff2"
--   -- mapM (iop . show) (constraints eff2)

  
--   return $ (all (`elem` constraints eff2) $ constraints eff1) &&  ((==0) . length . filter (not . (\eff -> eff ^. _before == [] && eff ^. _after == [])) $ eff)

showEffects = unlines . map (render . P.stackEffectNice . fst)

showClasses :: ParseState -> String
showClasses st = 
  let classesToMethods = views _classInterfaces M.toList st 
      classesToFields  = views _classFields M.toList st
      in
   render . vcat $ map (\((clazz, methods),(_,fields)) -> P.showClass clazz "unknown" fields methods) $ filter (\((class1, _), (class2, _)) -> class1 == class2) $ liftM2 (,) classesToMethods classesToFields

showCheckerState :: ParseState -> String
showCheckerState st = unlines [showDefinitions st, showClasses st]
showDefinitions :: ParseState -> String
showDefinitions st =
  let showColonDefinition name colonDef = render $ text name $+$ P.nested (P.colonDefinition' colonDef)
      showCreate name effs = render $ text name $+$ P.nested (vcat $ map P.stackEffectNice effs)
      keysValues = M.toList $ view _definedWords' st :: [(String, Definition)]
      in
  "DICTIONARY:\n\n" ++ (unlines . map (++ "\n") . map (\(name,y) -> case y of 
                                      ColDef x -> showColonDefinition name x
                                      CreateDef x -> showCreate name x) $ keysValues)


-- showEffs =  mapM (iop . (\(c,e) -> render $ P.stackEffect c $+$ P.stackEffect e))
-- showEffs' =  mapM (iop . render . P.stackEffect)
-- showEff =  iop . render . P.stackEffect

-- effectMatches :: StackEffect -> StackEffect -> CheckerM' Bool
-- effectMatches eff1 eff2 = handling _TypeClash (const $ return False) $ withEmpty''' $ do
--   let before' = StackEffect [] [] (eff1 ^. _before)
--       after' = StackEffect (eff1 ^. _after) [] []
--   checkEffects' <- view _2 :: CheckerM' CheckEffectsT
--   lift $ (`runReaderT` defCheckEffectsConfig) $ do
--     checkEffects' $ withoutIntersect [(before', StackEffect [] [] [])]
--     checkEffects' $ withoutIntersect [(eff2, StackEffect [] [] [])]
--     checkEffects' $ withoutIntersect [(after', StackEffect [] [] [])]
--   s <- lift getState
--   let eff = map fst (s ^. _effects._Wrapped._1)
--   iop "Das sind die effekte:"
--   iop $ show eff



--   iop " eff1"
--   showEffs' [eff1]
--   iop $ "constraints eff1"

--   mapM (iop . show) (constraints eff1)
--   iop $ "constraints eff2"
--   mapM (iop . show) (constraints eff2)
--   return $ (all (`elem` constraints eff2) $ constraints eff1) &&  ((==0) . length . filter (not . (\eff -> eff ^. _before == [] && eff ^. _after == [])) $ eff)
