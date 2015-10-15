{-# LANGUAGE   FlexibleContexts  #-}

module TF.StackEffectParser (
    parseAssertion'
  , defParseStackEffectsConfig
  , parseEffect
  , getEffect
  , parseCast'
  , parseFieldType)
       where

import           Control.Arrow hiding (left)
import Control.Error
import Control.Monad.Error.Lens
import           Control.Monad.State
import           Control.Monad.Reader
import           Data.Char hiding (Control)
import           Control.Lens hiding (to, from,noneOf)
import           TF.Types as T 
import           TF.ForthTypes as FT
import           TF.Util
import           Text.Parsec as P
import Data.List
import Debug.Trace

import TF.Errors



atLeastOneSpace = many1 space

rParenIS = "<paren>"
quoteIS = "<\">"

parseInputStreamArgument :: ParseStackEffectsM (Either c (Either DefiningArg StreamArg))
parseInputStreamArgument = do
    let streamMarker = "'"
        definedWordMarker = "D'"
        markDelimitingString = "<"

    let knownEffect = do 
          oldState <- getState
          putState def
          _ <- parseStackEffect
          newState <- getState
          let from' = newState ^. currentEffect.before
              to'   = newState ^. currentEffect.after
          putState oldState
          return $ StackEffect (concat $ concat from') [] (concat $ concat to') :: ParseStackEffectsM StackEffect

    let parseEndDelimiter = option Nothing $
                            fmap Just $
                              try (string rParenIS *> return ")") <|>
                              try (string quoteIS *> return "\"")
    let definingArg = do
          try (string definedWordMarker) <|> string (map toLower definedWordMarker)
          n' <- many1 $ noneOf $ streamMarker ++ markDelimitingString
          endDelimiter <- parseEndDelimiter
          string streamMarker
          createType <- optionMaybe $ do
            string ":["
            result <- parseCreateType
            string "]"
            return result
          -- runtimeEff <- parseRuntimeType
          -- return $ _Defining # DefiningArg n' Nothing (Left Nothing) endDelimiter Nothing runtimeEff False :: ParseStackEffectsM (Either DefiningArg StreamArg)
          return $ _Defining # DefiningArg n' Nothing createType endDelimiter Nothing Nothing :: ParseStackEffectsM (Either DefiningArg StreamArg)

    let notDefiningArg = do 
          string streamMarker 
          n' <- many1 $ noneOf $ streamMarker ++ markDelimitingString
          endDelimiter <- parseEndDelimiter
          string streamMarker
          runtimeEff <- parseRuntimeType
          return $ _NotDefining # StreamArg n' Nothing endDelimiter runtimeEff

    result <- try definingArg <|> notDefiningArg
    atLeastOneSpace
    return $ _StreamArg # result

parseStackEffects :: ParseStackEffectsM String
parseStackEffects = try (parseStackEffects' ('/', False)) <|> parseStackEffects' ('&', True)

parseStackEffects' :: (Char, Bool) -> ParseStackEffectsM String
parseStackEffects' (delimiter, isIntersect') = do
  string "("

  parseStackEffect `sepBy` P.char delimiter
                             

  modifyState $ isIntersect .~ isIntersect'

  string ")"


typeWithIndex :: BasicType -> ParseStackEffectsM IndexedStackType
typeWithIndex type' = do
  degreeRef <- length <$> many (P.char '*')
  let type'' = (!! degreeRef) . iterate Reference $ if (has _PrimType type' && type' ^?! _PrimType.symbol == FT.X) then Wildcard else NoReference type'
  string $ case type' of
              ClassType clazz -> clazz
              PrimType primType -> view asString primType
              ExecutionType _ -> "xt"
  index <- optionMaybe (fmap digitToInt digit) 
  return (type'', index)

-- a list of parsers which parse a string indicating a single type
singleTypes :: ParseStackEffectsM [ParseStackEffectsM IndexedStackType]
singleTypes =  do
  types' <- view types <$> getState


  classNames' <- view classNames
  let primTypes = map (try . typeWithIndex . (_PrimType # )) types' 
      classTypes =  map (try . typeWithIndex . (_ClassType # )) classNames'
  return $ (try executionTypeWithIndex) : (primTypes ++ classTypes)

-- a list of parsers which parse either a single type or alternative types like "type1|type"
alternativeTypes :: ParseStackEffectsM [ParseStackEffectsM [IndexedStackType]]
alternativeTypes = do
  singleTypes' <- singleTypes
  return $ (`map` singleTypes') $ \firstTypeParser -> try $ do
    firstType <- firstTypeParser
    alternativeType <- option [] $
                        P.char '|' *>
                        fmap (:[]) (choice singleTypes')

    atLeastOneSpace
    return $ firstType : alternativeType
                
  
parseStackEffect
  :: ParseStackEffectsM ()
parseStackEffect = do
  c' <- view currentEffect <$> getState
  unless (c' == def) $ modifyState $ previousEffects %~ (c' : )
  modifyState $ currentEffect .~ def

  let s = currentEffect -- define a short lens for the current effect
  
  atLeastOneSpace

  alternativeTypes' <- alternativeTypes

  let parseSingleSemiEffectBefore :: ParseStackEffectsM SingleSemiEffect
      parseSingleSemiEffectBefore = 
        many  . labeled  "type symbols seperated by spaces or input stream arguments" $ parseInputStreamArgument <|> ((_DataType #) <$> choice alternativeTypes') 

      parseSingleSemiEffectAfter :: ParseStackEffectsM [[IndexedStackType]]
      parseSingleSemiEffectAfter = many . labeled  "type symbols seperated by spaces" . choice $ alternativeTypes'

      parseSemiEffects p = p `sepBy` (P.char '|' >> atLeastOneSpace)

  dataTypesAndStreamArgs <- parseSemiEffects parseSingleSemiEffectBefore 

  let (typesBefore, streamArgs) = unzip . map (lefts &&& rights) $ dataTypesAndStreamArgs

  modifyState $ s.before .~  typesBefore
  modifyState $ s.streamArguments .~ streamArgs

  forced'' <-  (try (return False <* string "--") <|>
                  return True <* string "-!-")
  modifyState $ forced' .~ forced''
  atLeastOneSpace

  typesAfter <- parseSemiEffects parseSingleSemiEffectAfter
  modifyState $ s.after .~  typesAfter



parseRuntimeType :: ParseStackEffectsM (Maybe RuntimeSpecification)
parseRuntimeType = optionMaybe $ do
  string ":["

  let knownEffect = do 
        oldState <- getState
        putState def
        _ <- parseStackEffect
        newState <- getState
        let from' = newState ^. currentEffect.before
            to'   = newState ^. currentEffect.after
        putState oldState
        return $ _KnownR # StackEffect (concat $ concat from') [] (concat $ concat to') :: ParseStackEffectsM RuntimeSpecification
  let unknownEffect = do
        atLeastOneSpace
        string "EFF"
        index <- option (-1) (fmap digitToInt digit)  -- TODO index?!
        atLeastOneSpace
        return $ _UnknownR # index
  result <- try unknownEffect <|> knownEffect
  string "]"
  return result

executionTypeWithIndex :: ParseStackEffectsM IndexedStackType 
executionTypeWithIndex = do
    degreeRef <- length <$> many (P.char '*')
    string "xt"
    runtimeEff <- parseRuntimeType

    let type'' = (!! degreeRef) . iterate Reference $ NoReference $ ExecutionType (ExecutionToken FT.XD runtimeEff)
    index <- optionMaybe (fmap digitToInt digit) 
    return (type'', index)

defParseStackEffectsConfig :: ParseStackEffectsConfig
defParseStackEffectsConfig = ParseStackEffectsConfig [] False False

getEffect :: String -> IO StackEffect
getEffect t = do
             let (Right st) = runStackEffectParser t defParseStackEffectsConfig
                 eff = st ^. currentEffect

                 (from'', to'') = (^.before) &&& (^.after) $ eff :: ([[[IndexedStackType]]], [[[IndexedStackType]]])
                 (from', to') = head $ TF.StackEffectParser.allEffects $ (from'', to'') :: ([IndexedStackType], [IndexedStackType])
             return $ StackEffect  from' (eff ^. streamArguments._head) to'

-- | Relativ unleserliches StackEffect Parsing Resultat
testEffect :: String -> IO ()
testEffect t = do
  let result = flip runReader defParseStackEffectsConfig $ (runParserT (parseStackEffects >> getState) def "" t)
  -- let result = runStackEffectParser t defParseStackEffectsConfig
  case result of
    Left err -> print err
    Right st -> 
      forM_ (st^.currentEffect : st^.previousEffects) $ \x -> do
      print $ x^.before
      print $ x^.streamArguments
      print $ x^.after
      print $ st^.forced'


parseFieldType t config = parseEffectTemplate t config parseFieldType'

parseCast' t config = do
  iop "parseCast"
  parseEffectTemplate t config parseCast''
                          
parseAssertion' t config = do
  iop "parseassertion'"
  parseEffectTemplate t config parseAssertion''

parseCreateType :: ParseStackEffectsM IndexedStackType
parseCreateType = do
  atLeastOneSpace
  singleTypes' <- singleTypes
  parsedType <- choice singleTypes'
  atLeastOneSpace
  return parsedType

parseStackImage :: ParseStackEffectsM [[IndexedStackType]]
parseStackImage = do
  alternativeTypes' <- alternativeTypes
  stackImage <- many  . labeled  "type symbols seperated by spaces" $ choice alternativeTypes' 
  return stackImage

parseCast'' :: ParseStackEffectsM ()
parseCast'' = void $ do
  string "("
  atLeastOneSpace
  string "cast"

  parseStackEffect `sepBy` P.char '/'

  string ")"
  
  
parseAssertion'' :: ParseStackEffectsM ()
parseAssertion'' = void $ do 
  -- liftIO $ mapM print inputs
  string "("
  atLeastOneSpace

  forced <- try (string "assert!") *> return True <|> string "assert" *> return False
  atLeastOneSpace

  results <- parseStackImage `sepBy1` P.char '/' 

  traceM $ "Length: " ++ show (length results)

  let assertions = for results $ \t -> def & before .~ [[]] & after .~ [t] & streamArguments .~ [[]]

  modifyState $ currentEffect .~ head assertions
  modifyState $ previousEffects .~ tail assertions

  modifyState $ forced' .~ forced
  string ")"

parseFieldType' :: ParseStackEffectsM ()
parseFieldType' = void $ do
  string "("
  atLeastOneSpace
  -- types' <- view (currentEffect.types) <$> getState
  -- classNames' <- view classNames


  singleTypes' <- singleTypes
  fieldType <- choice singleTypes'
  modifyState $ currentEffect.before .~ [[]]
  modifyState $ currentEffect.streamArguments .~ [[]]
  modifyState $ currentEffect.after .~ [[[fieldType]]]
  atLeastOneSpace
  string ")"
                           
-- parseEffectTemplate :: String -> ParseStackEffectsConfig -> Script' ParseEffectResult
parseEffectTemplate t conf p = do
  -- iop "parseeffectemplate"

  allowDynamic <- view allowDynamicInStackComments
  initialState <- if allowDynamic then
                    return $ def & types %~ (FT.dyn :)
                  else
                    return def
  let parseResult = flip runReader conf $ (runParserT (p >> getState) initialState "" t)
  case parseResult of
    Left e -> do
      -- iop "parseeffectemplate wrong"
      iopS e
      throwing _ParseErr'  . show $ e
    Right st -> do
        -- iop "parseeffectemplate right"
        let streamArgsLists = view (traverse.streamArguments) allEffects
            sameStreamArgs = length (group streamArgsLists) <= 1
        when (not sameStreamArgs) $
          throwing _NotSameStreamArgs t -- every stack effect must
          -- have the same stream args

        return $ ParseEffectResult allEffectsCombos streamArgs (st^.forced') (st^.isIntersect)
       where
         allEffects = st^.currentEffect : st^.previousEffects
         streamArgs :: [DefiningOrNot]
         streamArgs = head . view (currentEffect.streamArguments) $ st
         allEffectsCombos :: [([IndexedStackType], [IndexedStackType])]
         allEffectsCombos = concat $
                for allEffects $
                (^.before) &&& (^.after) >>> TF.StackEffectParser.allEffects

parseEffect :: String -> ParseStackEffectsConfig -> Script' ParseEffectResult
parseEffect t conf = parseEffectTemplate t conf parseStackEffects

-- creates all combinations of the ("before","after")-word-operation-semi effects to get all possible stack effects
allEffects i' = [(f''',t''') | f'' <- f', f''' <- f'', t'' <- t', t''' <- t'']
        where 
           (f',t') = i' & both %~ map sequence

runStackEffectParser :: String -> ParseStackEffectsConfig -> Either ParseError ParseStacksState
runStackEffectParser t config = flip runReader config $ runParserT (parseStackEffects >> getState) def "" t
                                           

