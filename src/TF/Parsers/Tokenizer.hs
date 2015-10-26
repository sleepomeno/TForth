{-# LANGUAGE  FlexibleContexts #-}

module TF.Parsers.Tokenizer (parseWords) where


import Control.Lens hiding (noneOf,(??))
import           Control.Error as E
import           TF.WordsBuilder (buildWord')
import Control.Monad.Except
import           Control.Monad.Error.Lens
import           Control.Monad.Free
import           Data.Char hiding (Control)
import qualified Data.Map as M
import           TF.Types hiding (state)
import qualified TF.Words as W
import qualified Data.Text as Te
import           Text.Parsec hiding (runParser, anyToken)
import TF.Errors

import TF.Type.Nodes


wordIdentifier :: ParsecT String () Script' String
wordIdentifier = do
  startingDigits <- many digit
  letters <- many1 (satisfy neitherDigitNorSpace)
  lettersOrDigits <- many (satisfy (not . isSpace))
  return $ startingDigits ++ letters ++ lettersOrDigits

parseLineComment :: ParsecT String () Script' ()
parseLineComment = do
  string "\\"
  manyTill anyChar (try newline)
  return ()

parseNextToken = (liftM (const Nothing) $ try parseLineComment) <|> (liftM Just parseNextWord)

parseNextWord :: ParsecT String () Script' Token
parseNextWord = do
    let parseToken :: ParsecT String () Script' Token
        parseToken = do
          w' <- (Te.toLower . Te.pack) <$> wordIdentifier
          coreWords <- use _wordsMap
          let possibleWord = M.lookup (WordIdentifier w') coreWords
          return $ maybe (UnknownToken . Unknown . Te.unpack $ w')
                         WordToken
                         possibleWord
    number <- (view word) <$> (lift $ buildWord' W.number)
    try parseToken <|> (int *> (return . WordToken $ number))

neitherDigitNorSpace x = not $ isDigit x || isSpace x


int = rd <$> (minusP <|> numberP)
    where rd     = read :: String -> Int

minusP  = (:) <$> Text.Parsec.char '-' <*> numberP
numberP = many1 digit


-- | Main parsing function called from outside
parseProgram' :: ParsecT String () Script' [Token]
parseProgram' = liftM catMaybes (parseNextToken `sepEndBy` spaces)

-- | parseWords returns a list of `Token`s
parseWords :: String -> Script' [Token]
parseWords t = do
  additionalWordsDefinitions <- view thirdParty  :: Script' [Free WordDefinition ()]
  additionalWords <- mapM (fmap (view word) . buildWord') additionalWordsDefinitions

  coreWordsByIdentifier <- W.coreWordsByIdentifier
  let coreWords' = foldl (\m w -> M.insert (w ^. _parsedW) w m) coreWordsByIdentifier additionalWords

  _wordsMap .= coreWords'
  result <- runParserT parseProgram' () "" t 
  lift $ either (throwing _ParseErr' . show) return result
