{-# LANGUAGE LambdaCase,OverloadedStrings, TupleSections, DeriveDataTypeable, TypeFamilies, FunctionalDependencies, RecordWildCards, FlexibleContexts, RankNTypes, TemplateHaskell,  DeriveFunctor, NoMonomorphismRestriction, FlexibleInstances #-}

module TF.Parsers.Tokenizer (parseWords) where

import           Control.Applicative hiding (optional, (<|>),many)

import Control.Lens hiding (noneOf,(??))
import           Control.Error as E
import           TF.WordsBuilder (buildWord')
import Control.Monad.Except
import           Control.Monad.Error.Lens
import           Control.Monad.Free
-- import           Control.Monad.Trans.Free
import           Data.Char hiding (Control)
import qualified Data.Map as M
import qualified Data.Set as S
import           TF.Types hiding (state, isSubtypeOf)
import qualified TF.Types as T
import qualified TF.Words as W hiding (coreWords')
import           TF.Checker (checkNodes)
import           TF.CheckerUtils (withEmpty)
import  TF.Util
import qualified Data.Text as Te
import           Text.Parsec hiding (runParser, anyToken)
import TF.Errors


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

parseNextToken = do
  (liftM (const Nothing) $ try parseLineComment) <|> (liftM Just parseNextWord)

parseNextWord :: ParsecT String () Script' Token
parseNextWord = do
    let parseToken :: ParsecT String () Script' Token
        parseToken = do
          w' <- (Te.toLower . Te.pack) <$> wordIdentifier
          coreWords <- use wordsMap
          let possibleWord = M.lookup (new _WordIdentifier w') coreWords
          return $ maybe (new _Unknown . Unknown . Te.unpack $ w')
                         (new _Word)
                         possibleWord
    -- number <- (view word) <$> (lift $ local (allCoreDynamic .~ False) $ buildWord' W.number)
    number <- (view word) <$> (lift $ buildWord' W.number)
    try parseToken <|> (int *> (return . (new _Number) $ number))

neitherDigitNorSpace x = not $ isDigit x || isSpace x


int = rd <$> (minusP <|> numberP)
    where rd     = read :: String -> Int

minusP  = (:) <$> Text.Parsec.char '-' <*> numberP
numberP = many1 digit


-- | Main parsing function called from outside
parseProgram' :: ParsecT String () Script' [Token]
parseProgram' = liftM catMaybes (parseNextToken `sepEndBy` spaces)

-- | parseWords returns a list of `Either Unknown (Word Semantics)`
parseWords :: String -> Script' [Token]
parseWords t = do
  additionalWordsDefinitions <- view thirdParty  :: Script' [Free WordDefinition ()]
  additionalWords <- mapM (fmap (view word) . buildWord') additionalWordsDefinitions

  coreWordsByIdentifier <- W.coreWordsByIdentifier
  let coreWords' = foldl (\m w -> M.insert (view parsed w) w m) coreWordsByIdentifier additionalWords

  wordsMap .= coreWords'
  result <- runParserT parseProgram' () "" t 
  lift $ either (throwing _ParseErr' . show) return result
