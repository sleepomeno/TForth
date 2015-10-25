{-# LANGUAGE LambdaCase,OverloadedStrings, TupleSections   #-}

module TF.Parsers.Parser (
  parseProgram
  ) where

import Prelude hiding (Word)

import Control.Lens hiding (noneOf,(??))
import Lens.Family.Total hiding ((&))
import           Control.Error as E
import Data.Monoid
import TF.Evaluator
import           TF.StackEffectParser (defParseStackEffectsConfig)
import           Control.Monad.State hiding (state)
import           Control.Monad.Reader (local, runReaderT)
import           Control.Monad.Error.Lens
-- import           Control.Monad.Trans.Free
import qualified Data.Map as M
import           TF.Types hiding (state, isSubtypeOf)
import qualified TF.Words as W 
import           TF.Checker (checkNodes)
import           TF.CheckerUtils (withEmpty)
import  TF.Util
import qualified Data.Text as Te
import           Text.Parsec hiding (runParser, anyToken, (<|>))
import TF.Errors

import TF.Parsers.OOP
import TF.Parsers.ControlStructures
import TF.Parsers.ParserUtils
import TF.Parsers.Create
import TF.Parsers.Misc
import TF.Type.StackEffect
import TF.Type.Nodes

parseProgram :: CheckerM ([Node], ParseState)
parseProgram = do
  coreWords <- lift W.coreWordsByIdentifier :: CheckerM (M.Map Parsable Word)
  _wordsMap .= coreWords  
  forthWordsOrExprs <- many parseNode
  st <- getState
  let effs = toListOf (_effects._Wrapped._1.traverse._2) st
      allBeforesEmpty :: Bool
      allBeforesEmpty = all (null . view _before) effs

  effectsValid <- views topLevelEmpty ((allBeforesEmpty ||) . not)
  if effectsValid then
    return (forthWordsOrExprs, st)
  else
    liftUp $ throwing _UnemptyStack ("Top Level", "'Before's of top level stack effects must be empty!")

parseNode :: CheckerM Node
parseNode = parseNodeWithout []

parseNodeWithout :: [Word] -> CheckerM Node
parseNodeWithout ws = withTrace $ do
  node <- withEmpty $ liftM Expr expression </> liftM ForthWord (evalForthWordWithout ws)

  applyTypeChecking node
  return node

applyTypeChecking node = do 
  doTypeChecking <- view typeCheck

  when doTypeChecking $ void $ 
    checkNodes [node]

  
try' expr = lift . try $ (expr `runReaderT` env)
env = ExpressionEnv parseWord isKnownWord parseStackEffectSemantics parseNode parseNodeWithout

expression :: CheckerM Expr
expression = (`runReaderT` env) $ parsePostpone </> try' parseIfElse </> try' parseIf  </> parseColon </> try' parseExecute </> try' parseAssertion </> try' parseCast </>  try' parseTick </> try' parseDoLoop </> try' parseDoPlusLoop </> try' parseBeginUntil </> try' parseBeginWhileRepeat </> parseInterpreted </> try' parseFieldCall </> try' parseMethodCall </> try' parseNewObject </> try' parseSuperclassMethodCall </> try' parseClass </> try' parseNoName </> try' parseCreating  </> try' parseInclude </> try' parseRequire

parseWord :: Te.Text -> CheckerM ParsedWord
parseWord w = do
  coreWords <- use _wordsMap
  let maybeWord = M.lookup (WordIdentifier w) coreWords
  when (isNothing maybeWord) $ throwing _Impossible ("Did not find word " <> Te.unpack w)
  let w'' = maybeWord ^?! _Just
    
  (WordToken w') <- satisfy' (== WordToken w'')
  (KnownWord pw, _) <- evalKnownWord  w' 
  return pw

isKnownWord :: CheckerM (Maybe (Either ForthWord DefOrWord) )
isKnownWord              = do
  possWord <- anyToken
  s        <- getState
  let maybeColonDefinition' :: Unknown -> Maybe ColonDefinitionProcessed
      maybeColonDefinition' (Unknown unknownName)   = preview (_definedWords'.at unknownName._Just._ColDef) s
  maybeDefOrWord <- case possWord of
    UnknownToken uk@(Unknown unknownName) -> do 
        iopP $ unknownName

        runMaybeT $ do
            y <- hoistMaybe $ maybeColonDefinition' uk
            let immediate = y ^. colonDefinition.meta.isImmediate
            if immediate then do
                forthWord <- lift $ evalColonDefinition  (y & colonDefinition.meta.isImmediate .~ False)
                return $ Left forthWord
            else 
        -- _Def
                return $ Right . DefinitionName $ y ^. colonDefinition.meta.name

    WordToken word -> do
      if word ^. _isImmediateWord then do 
        (forthWord, _) <- evalKnownWord (word & _isImmediateWord .~ False)
        return $ Just . Left $ forthWord
      else 
        return $ Just . Right . WordName . view _nameW $ word

  iopP $ show maybeDefOrWord
  return maybeDefOrWord
    
parseStackEffectString = do
  local (readFromStream .~ False) $ parseWord "("
  commentBody <- manyTill anyToken (parseUnknown ")") 
  let commentBody' = map possWordAsString commentBody
      result = ("( " ++ ) . (++ " )") . unwords $ commentBody'
  return result

type UnresolvedArgsM = StateT (M.Map Int UniqueArg) CheckerM 
  
prepareUnresolvedArgsTypes :: (Semantics, Bool) -> CheckerM (Semantics, Bool)
prepareUnresolvedArgsTypes (sem, forced) = do
  effs <- (`evalStateT` M.empty) $ forM (sem ^. (_semEffectsOfStack._stefwiMultiEffects._Wrapped)) go
  return (sem & _semEffectsOfStack._stefwiMultiEffects._Wrapped .~ effs, forced)
  where

    go :: StackEffect -> UnresolvedArgsM StackEffect
    go eff = do
      bs <- mapM indexedStackType' $ eff ^. _before
      args <- mapM definingOrNot $ eff ^. _streamArgs
      as <- mapM indexedStackType' $ eff ^. _after
      return $ eff & _streamArgs .~ args & _before .~ bs & _after .~ as

    definingOrNot :: DefiningOrNot -> UnresolvedArgsM DefiningOrNot
    definingOrNot = \case
      arg@(NotDefining (StreamArg (ArgInfo _ _ _ )(Just (UnknownR index)))) -> do
        newIndex <- getIndex index
        return $ arg & _NotDefining._runtimeSpecified._Just._UnknownR .~ newIndex
      arg -> return arg
            
    indexedStackType' :: IndexedStackType -> UnresolvedArgsM IndexedStackType
    indexedStackType' (IndexedStackType arg@(NoReference (ExecutionType (ExecutionToken _ (Just (UnknownR index))))) i) = do
      newIndex <- getIndex index
      return $ IndexedStackType (arg & _NoReference._ExecutionType._exectokenRuntimeSpecified._Just._UnknownR .~ newIndex) i
    indexedStackType' x = return x

    getIndex index = do 
      index' <- use (at index)  :: UnresolvedArgsM (Maybe Int)
      case index' of
        Just index'' -> return index''
        Nothing      -> do
          uniqueIdentifier <- lift $ _identifier <<+= 1
          at index ?= uniqueIdentifier
          return uniqueIdentifier
      
parseStackEffectSemantics :: (String -> ParseStackEffectsConfig -> Script' ParseEffectResult) -> CheckerM (Semantics, Bool)
parseStackEffectSemantics p = do
  stackEffect' <- parseStackEffectString   :: CheckerM String
  iop $ "stackeffect-string:"
  iop $ stackEffect'

  classes' <- views _classInterfaces (map fst . M.toList) <$> getState
  classes'' <- views _classFields (map fst . M.toList) <$> getState
  dynamic <- view allowDynamicInStackComments
  effect''' <- handling _ParseErr' (unexpected . show) (lift $ p stackEffect' (defParseStackEffectsConfig & classNames .~ (classes' ++ classes'') & allowDynamicInStackComments .~ dynamic ))
  let effect' = getSemantics effect'''
  prepareUnresolvedArgsTypes effect'
  where
    getSemantics :: ParseEffectResult -> (Semantics, Bool)
    getSemantics (ParseEffectResult parsedEffects streamArgs forcedEffect isIntersect) = let 

                              effects' =  parsedEffects  & traverse %~ (\(b,a) -> StackEffect (reverse b) streamArgs (reverse a))
                     in
                       (def :: Semantics) & _semEffectsOfStack._stefwiMultiEffects._Wrapped .~ effects'  & (, forcedEffect)

