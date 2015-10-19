{-# LANGUAGE   FlexibleContexts  #-}

module TF.StackEffectParser (
    parseAssertion'
  , defParseStackEffectsConfig
  , parseEffect
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

import TF.Type.StackEffect


atLeastOneSpace = many1 space

rParenIS = "<paren>"
quoteIS = "<\">"

parseKnownEffect = do
          oldState <- getState
          putState def
          _ <- parseStackEffect
          newState <- getState
          let from' = newState ^. _currentEffect._parsestateBefore
              to'   = newState ^. _currentEffect._parsestateAfter
          putState oldState
          return (from',to')

parseInputStreamArgument :: ParseStackEffectsM (DataArgOrStreamArg [IndexedStackType])
parseInputStreamArgument = do
    let streamMarker = "'"
        definedWordMarker = "D'"
        markDelimitingString = "<"

    -- let knownEffect = do 
    --       (from',to') <- parseKnownEffect
    --       return $ StackEffect (concat $ concat from') [] (concat $ concat to') :: ParseStackEffectsM StackEffect

    let parseEndDelimiter = option Nothing $
                            fmap Just $
                              try (string rParenIS *> return ")") <|>
                              try (string quoteIS *> return "\"")
    let parseArg = do
          name <- many1 $ noneOf $ streamMarker ++ markDelimitingString
          endDelimiter <- parseEndDelimiter
          string streamMarker
          return (name,endDelimiter)
    let definingArg = do
          try (string definedWordMarker) <|> string (map toLower definedWordMarker)
          (n',endDelimiter) <- parseArg
          createType <- optionMaybe $ do
            string ":["
            result <- parseCreateType
            string "]"
            return result
          return $ Defining (DefiningArg (ArgInfo n' Nothing endDelimiter Nothing) createType Nothing) :: ParseStackEffectsM DefiningOrNot

    let notDefiningArg = do 
          string streamMarker 
          (n',endDelimiter) <- parseArg
          runtimeEff <- parseRuntimeType
          return $ NotDefining $ StreamArg (ArgInfo n' Nothing endDelimiter runtimeEff)

    result <- try definingArg <|> notDefiningArg
    atLeastOneSpace
    -- return $ _StreamArg # result
    return $ NonDataArg result

parseStackEffects :: ParseStackEffectsM String
parseStackEffects = try (parseStackEffects' ('/', False)) <|> parseStackEffects' ('&', True)

parseStackEffects' :: (Char, Bool) -> ParseStackEffectsM String
parseStackEffects' (delimiter, isIntersect') = do
  string "("

  parseStackEffect `sepBy` P.char delimiter
                             

  modifyState $ _isIntersect .~ isIntersect'

  string ")"


typeWithIndex :: BasicType -> ParseStackEffectsM IndexedStackType
typeWithIndex type' = do
  degreeRef <- length <$> many (P.char '*')
  let type'' = (!! degreeRef) . iterate Reference $ if (has _PrimType type' && type' ^?! (_PrimType._primtypeSymbol) == FT.X) then Wildcard else NoReference type'
  string $ case type' of
              ClassType clazz -> clazz
              PrimType primType -> view _asString primType
              ExecutionType _ -> "xt"
  index <- optionMaybe (fmap digitToInt digit) 
  return (type'', index)

-- a list of parsers which parse a string indicating a single type
singleTypes :: ParseStackEffectsM [ParseStackEffectsM IndexedStackType]
singleTypes =  do
  types' <- view _types <$> getState


  classNames' <- view classNames
  let primTypes = map (try . typeWithIndex . PrimType ) types' 
      classTypes =  map (try . typeWithIndex . ClassType ) classNames'
  return $ try executionTypeWithIndex : (primTypes ++ classTypes)

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
  c' <- view _currentEffect <$> getState
  unless (c' == def) $ modifyState $ _previousEffects %~ (c' : )
  modifyState $ _currentEffect .~ def

  let s = _currentEffect -- define a short lens for the current effect
  
  atLeastOneSpace

  alternativeTypes' <- alternativeTypes

  let parseSingleSemiEffectBefore :: ParseStackEffectsM SingleSemiEffect
      parseSingleSemiEffectBefore = 
        many  . labeled  "type symbols seperated by spaces or input stream arguments" $ parseInputStreamArgument <|> (DataArg <$> choice alternativeTypes') 

      parseSingleSemiEffectAfter :: ParseStackEffectsM [[IndexedStackType]]
      parseSingleSemiEffectAfter = many . labeled  "type symbols seperated by spaces" . choice $ alternativeTypes'

      parseSemiEffects p = p `sepBy` (P.char '|' >> atLeastOneSpace)

  dataTypesAndStreamArgs <- parseSemiEffects parseSingleSemiEffectBefore 

  let (typesBefore, streamArgs) = unzip . map ((lefts &&& rights) . map (view argIso)) $ dataTypesAndStreamArgs

  modifyState $ s._parsestateBefore .~  typesBefore
  modifyState $ s._parsestateStreamArguments .~ streamArgs

  forced'' <-  (try (return False <* string "--") <|>
                  return True <* string "-!-")
  modifyState $ _forced' .~ forced''
  atLeastOneSpace

  typesAfter <- parseSemiEffects parseSingleSemiEffectAfter
  modifyState $ s._parsestateAfter .~  typesAfter



parseRuntimeType :: ParseStackEffectsM (Maybe RuntimeSpecification)
parseRuntimeType = optionMaybe $ do
  string ":["

  let knownEffect = do 
        (from',to') <- parseKnownEffect
        return $ KnownR $ StackEffect (concat $ concat from') [] (concat $ concat to') :: ParseStackEffectsM RuntimeSpecification
  let unknownEffect = do
        atLeastOneSpace
        string "EFF"
        index <- option (-1) (fmap digitToInt digit)  -- TODO index?!
        atLeastOneSpace
        return $ UnknownR index
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

-- | Relativ unleserliches StackEffect Parsing Resultat
testEffect :: String -> IO ()
testEffect t = do
  let result = flip runReader defParseStackEffectsConfig $ (runParserT (parseStackEffects >> getState) def "" t)
  case result of
    Left err -> print err
    Right st -> 
      forM_ (st^._currentEffect : st^._previousEffects) $ \x -> do
      print $ x^._parsestateBefore
      print $ x^._parsestateStreamArguments
      print $ x^._parsestateAfter
      print $ st^._forced'


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

  let assertions = for results $ \t -> def & _parsestateBefore .~ [[]] & _parsestateAfter .~ [t] & _parsestateStreamArguments .~ [[]]

  modifyState $ _currentEffect .~ head assertions
  modifyState $ _previousEffects .~ tail assertions

  modifyState $ _forced' .~ forced
  string ")"

parseFieldType' :: ParseStackEffectsM ()
parseFieldType' = void $ do
  string "("
  atLeastOneSpace
  -- types' <- view (currentEffect.types) <$> getState
  -- classNames' <- view classNames


  singleTypes' <- singleTypes
  fieldType <- choice singleTypes'
  modifyState $ _currentEffect._parsestateBefore .~ [[]]
  modifyState $ _currentEffect._parsestateStreamArguments .~ [[]]
  modifyState $ _currentEffect._parsestateAfter .~ [[[fieldType]]]
  atLeastOneSpace
  string ")"
                           
parseEffectTemplate t conf p = do
  -- iop "parseeffectemplate"

  allowDynamic <- view allowDynamicInStackComments
  initialState <- if allowDynamic then
                    return $ def & _types %~ (FT.dyn :)
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
        let streamArgsLists = view (traverse._parsestateStreamArguments) allEffects
            sameStreamArgs = length (group streamArgsLists) <= 1
        when (not sameStreamArgs) $
          throwing _NotSameStreamArgs t -- every stack effect must
          -- have the same stream args

        return $ ParseEffectResult allEffectsCombos streamArgs (st^._forced') (st^._isIntersect)
       where
         allEffects = st^._currentEffect : st^._previousEffects
         streamArgs :: [DefiningOrNot]
         streamArgs = head . view (_currentEffect._parsestateStreamArguments) $ st
         allEffectsCombos :: [([IndexedStackType], [IndexedStackType])]
         allEffectsCombos = concat $
                for allEffects $
                (^._parsestateBefore) &&& (^._parsestateAfter) >>> TF.StackEffectParser.allEffects

parseEffect :: String -> ParseStackEffectsConfig -> Script' ParseEffectResult
parseEffect t conf = parseEffectTemplate t conf parseStackEffects

-- creates all combinations of the ("before","after")-word-operation-semi effects to get all possible stack effects
allEffects i' = [(f''',t''') | f'' <- f', f''' <- f'', t'' <- t', t''' <- t'']
        where 
           (f',t') = i' & both %~ map sequence

runStackEffectParser :: String -> ParseStackEffectsConfig -> Either ParseError ParseStacksState
runStackEffectParser t config = flip runReader config $ runParserT (parseStackEffects >> getState) def "" t
                                           

