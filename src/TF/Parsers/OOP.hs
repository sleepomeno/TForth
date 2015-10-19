{-# LANGUAGE LambdaCase,OverloadedStrings #-}


module TF.Parsers.OOP where


import Control.Lens hiding (noneOf,(??))
import           Control.Error as E
import Control.Arrow (second)
import Data.Monoid
import           TF.StackEffectParser (parseFieldType, parseEffect)
import           Control.Monad.State hiding (state)
import           Control.Monad.Error.Lens
-- import           Control.Monad.Trans.Free
import qualified Data.Map as M
import qualified Data.Set as S
import           TF.Types hiding (state, isSubtypeOf)
import qualified TF.Types as T
import  TF.Util
import           Data.Maybe
import           Text.Parsec hiding (Empty,runParser, anyToken)
import           TF.SubtypeUtil
import TF.Errors

import Control.Monad.Reader

import TF.Type.StackEffect
import TF.Type.Nodes
import TF.Parsers.ParserUtils


parseNoName :: ExpressionsM Expr
parseNoName = do
  parseKeyword ":noname"
  parseStackEffectSemantics <- view parseStackEffectSemantics'
  sem <- lift $ (_Just._1 %~ (view (_semEffectsOfStack._Wrapped))) <$> (optionMaybe $ parseStackEffectSemantics parseEffect)

  let parseDefines = do
        clazz <- parseClassName
        parseKeyword "defines"
        method <- parseMethodName clazz

        return (clazz, method)

  let parseNonameBody :: ExpressionsM (Either [Node] [Node])
      parseNonameBody = do
        lift $ modifyState $ set stateVar COMPILESTATE
        exprs <- Right <$> manyWordsTill ";"
        lift $ modifyState $ set stateVar INTERPRETSTATE
        return exprs

      typeCheckingFails :: String -> ExpressionsM (Either [Node] [Node])
      typeCheckingFails reason =  do
        iopP "typecheckingfails"
        env <- ask
        lift $ local (typeCheck .~ False) $ (`runReaderT` env) parseNonameBody
        lift $ modifyState $ set stateVar INTERPRETSTATE
        return $ Left []

  expr <- catches parseNonameBody (errorHandler typeCheckingFails ":Noname implementation")
  iopP "after parsenonamebody"
  -- inp <- getInput
  -- liftIO . mapM (putStrLn. show) $ inp
  (clazz, method) <- parseDefines

  return $ OOPExpr $ either (const $ NoNameClash sem clazz method)
                  (\expr -> NoName sem expr clazz method)
                  expr

parseVariable :: ExpressionsM (String, Maybe StackEffect)
parseVariable = do
  -- TODO support cell
  -- manyTill anyToken (parseKeyword "var")
  -- parseKeyword "cell"
  parseKeyword "var"
  -- parseKeyword "var"
  field <- parseUnknownName
  parseStackEffectSemantics <- view parseStackEffectSemantics'
  sem <- lift $ optionMaybe $ parseStackEffectSemantics parseFieldType
  -- iop $ show sem
  return (field, sem & fmap fst & _Just %~ (fromJust . preview (_semEffectsOfStack._Wrapped._head)))

parseMethod :: ExpressionsM (String, Maybe ([StackEffect], Bool))
parseMethod = do
  parseKeyword "method"
  method <- parseUnknownName
  parseStackEffectSemantics <- view parseStackEffectSemantics'
  sem <- lift $ optionMaybe $ parseStackEffectSemantics parseEffect
  return (method, sem & _Just._1 %~ view (_semEffectsOfStack._Wrapped))

parseEndClass :: ExpressionsM String
parseEndClass = do
  parseKeyword "end-class"
  parseUnknownName

checkFields :: ClassName -> ClassName -> [(Variable, OOFieldSem)] -> ExpressionsM ()
checkFields newClass oldClass fields = 
  forM_ fields $ \(fieldName, oofieldsem) -> 
    case oofieldsem of
     ByFieldDefinition eff -> do
       oldFields <- (toListOf $ traverse._1) <$> getFieldsOfClass oldClass :: ExpressionsM [Variable]
       when (fieldName `elem` oldFields) $ 
         throwing _RedefinedField fieldName

     InferredByField eff -> return () -- throwing _Impossible "Cannot be InferredByField here!"

checkMethods :: ClassName -> ClassName -> [(Method, OOMethodSem)] -> ExpressionsM ()
checkMethods newClass oldClass methods = do
  forM_ methods $ \(methodName, oomethodsem) -> do
    case oomethodsem of
     ByDefinition (effs, _) -> checkEffs effs methodName
     InferredByMethod (effs, _) -> checkEffs effs methodName
     Empty -> return ()
  where
    checkEffs :: [StackEffect] -> Method -> ExpressionsM ()
    checkEffs effs methodName = forM_ effs checkEff
      where
        checkEff :: StackEffect -> ExpressionsM ()
        checkEff eff = void $ lift $ runMaybeT $ do
              superclassMethod' <- lift $ preview (classInterfaces.at oldClass._Just.traverse.filtered (\(m, _) -> m == methodName))<$> getState  
              superclassMethodEffects <- (getEffsOfMethod . view _2) <$> hoistMaybe superclassMethod'
              forM_ superclassMethodEffects $ \superclassMethodEff -> do
                isSubtype' <- lift $ eff `effectIsSubtypeOf` superclassMethodEff
                unless isSubtype' $
                  throwing _MethodNotSubtypeOfSuperclassMethod ()

getEffOfField = \case
  ByFieldDefinition eff -> eff
  InferredByField eff -> eff

getEffsOfMethod :: OOMethodSem -> [StackEffect]
getEffsOfMethod oomethodsem = 
    case oomethodsem of
     ByDefinition (effs, _) -> effs
     InferredByMethod (effs, _) -> effs
     Empty ->  []

getNonOverwrittenMethods :: ClassName -> [Method] -> ExpressionsM [(Method, OOMethodSem)]
getNonOverwrittenMethods oldClass methods = do
  toListOf (classInterfaces.at oldClass._Just.traverse.filtered (\(m, _) -> m `notElem` methods)) <$> (lift getState) :: ExpressionsM [(Method, OOMethodSem)]
  
parseClass :: ExpressionsM Expr
parseClass = do
  oldClass <- parseClassName
  parseKeyword "class"
  uniqueIdentifier <- lift $ identifier <<+= 1
  uniqueIdentifier' <- lift $ identifier <<+= 1
  uniqueIdentifier'' <- lift $ identifier <<+= 1
  env <- ask
  let runExpression = (`runReaderT` env)
  variables' <- lift $ many (try (runExpression parseVariable))
  methods' <- lift $ many (try ((`runReaderT` env) parseMethod))
  -- inp <- getInput
  -- liftIO $ mapM_ (putStrLn . show) $ inp
  className <- parseEndClass
  -- let classType = (NoReference $ _ClassType # className, Just uniqueIdentifier')
  let classType = (NoReference $ ClassType className, Just uniqueIdentifier')

  let variables = map (second $ maybe (InferredByField $ StackEffect [classType] [] [(UnknownType uniqueIdentifier, Just uniqueIdentifier'')])
                       (ByFieldDefinition . over _before (classType:))) $ variables'
  let methods :: [(Method, OOMethodSem)]
      methods = map (second $ maybe Empty (ByDefinition . over (_1.traverse._before) (classType:))) $ methods' 

  checkMethods className oldClass methods
  checkFields className oldClass variables

  superclassMethodsNotOverwritten <- getNonOverwrittenMethods oldClass (methods ^.. traverse._1)
  
  lift $ modifyState $ over classInterfaces (M.insert className (methods ++ superclassMethodsNotOverwritten))
  fieldsOfSuperclass <- getFieldsOfClass oldClass
  lift $ modifyState $ over classFields (M.insert className (variables ++ fieldsOfSuperclass))

  lift $ modifyState $ over subtypeRelation (S.insert (ClassType className, ClassType oldClass))
  lift $ modifyState $ over subtypeRelation (S.insert (ClassType className, ClassType className))
  

  return $ OOPExpr $ Class className variables methods oldClass


getFieldsOfClass :: ClassName -> ExpressionsM [(Variable, OOFieldSem)]
getFieldsOfClass clazz = toListOf (classFields.at clazz._Just.traverse) <$> (lift getState) :: ExpressionsM [(Variable, OOFieldSem)]

parseNewObject :: ExpressionsM Expr
parseNewObject = do
  clazz <- parseClassName
  parseKeyword "new"
  -- compOrExec <- lift $ views stateVar (\sVar -> if sVar == INTERPRETSTATE then Right else Left) <$> getState
  compOrExec <- compOrExec'
  return $ OOPExpr $ NewObject $ compOrExec $ clazz

isMethod :: String -> ExpressionsM Bool
isMethod method = do
  keysValues <- lift $ views classInterfaces M.toList <$> getState
  let filtered = filter (\(_, methods) -> any (\(x,_) -> x == method) methods) keysValues :: [(ClassName, [(Method, OOMethodSem)])]
  return . not . null $ filtered

isField :: String -> ExpressionsM Bool
isField field = do
  keysValues <- lift $ views classFields M.toList <$> getState
  let filtered = filter (\(_, fields) -> any (\(x,_) -> x == field) fields) keysValues :: [(ClassName, [(Variable, OOFieldSem)])]
  return . not . null $ filtered

  
parseFieldCall :: ExpressionsM Expr
parseFieldCall = do 
  fieldName <- parseUnknownName
  isField' <- isField fieldName
  guard isField'
  compOrExec <- compOrExec'
  -- compOrExec <- lift $ views stateVar (\sVar -> if sVar == INTERPRETSTATE then new _Executed else new _Compiled) <$> getState
  return . OOPExpr . FieldCall . compOrExec $ fieldName

parseMethodCall :: ExpressionsM Expr
parseMethodCall = do
  methodName <- parseUnknownName
  isMethod' <- isMethod methodName
  guard isMethod'
  -- compOrExec <- lift $ views stateVar (\sVar -> if sVar == INTERPRETSTATE then new _Executed else new _Compiled) <$> getState
  compOrExec <- compOrExec'
  return .  OOPExpr . MethodCall . compOrExec $ methodName


parseSuperclassMethodCall :: ExpressionsM Expr
parseSuperclassMethodCall = do
  isInDefinition <- lift $ views stateVar (== COMPILESTATE) <$> getState
  parseWordLeftBracket
  clazz <- parseUnknownName
  parseKeyword "::"
  method <- parseUnknownName

  -- TODO add message to output when not in definition
  guard isInDefinition
  return $ OOPExpr $ SuperClassMethodCall clazz method

parseClassName :: ExpressionsM String
parseClassName = do
  className <- parseUnknownName
  s <-  lift getState
  let isClassKnown = getAny $ views (classInterfaces.to M.keys.traverse) (Any . (== className)) s 
  when (not isClassKnown) $ iopP $ "Class " ++ className ++ " is unknown!"
  guard isClassKnown
  return className


parseMethodName :: ClassName -> ExpressionsM String
parseMethodName className = do
  methodName <- parseUnknownName
  s <- lift getState
  let isMethodKnown = getAny $ views (classInterfaces.ix className.traverse._1)
                                     (Any . (== methodName)) s
  when (not isMethodKnown) $ iopP $ "Method " ++ methodName ++ " is not a method of class " ++ className
  guard isMethodKnown
  
  return methodName
