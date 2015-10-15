{-# LANGUAGE OverloadedStrings, FlexibleContexts, NoMonomorphismRestriction  #-}

module TF.Parsers.ParserUtils where

import Prelude hiding (Word, last)

import Control.Lens hiding (noneOf,(??), children)
import           Control.Error as E
import Data.Maybe (fromJust)
import qualified TF.Printer as P
import Data.Monoid
import Control.Monad.Except
import           Control.Monad.Error.Lens
import qualified Data.Map as M
import           TF.Types hiding (state, isSubtypeOf)
import           TF.CheckerUtils (withEmpty, withEmpty''')
import  TF.Util
import qualified Data.Text as Te
import           Text.Parsec hiding (runParser, anyToken)
import TF.Errors

import Data.Tree
import Data.Tree.Zipper hiding (after,before,first)
import  Text.PrettyPrint (render)
import Control.Arrow (first)

munzip mab = (liftM fst mab, liftM snd mab)
mzip (ma,mb) = do
  a <- ma
  b <- mb
  return (a,b)

withTrace' p = mzip . (first withTrace) . munzip $ p

withTrace p = do
  let modState f = modifyState $ trace._Wrapped %~ f
  modState $insert (Node "" []) . last . children
  result <- p
  modState $ modifyTree (\t -> t { rootLabel = render $ P.infoNode result })
  modState $ \s ->
    if isContained s then
      fromJust $ parent s
    else
      s
  return result

parseKeyword :: String -> ExpressionsM ()
parseKeyword keyword = do
  Left uk <- lift $ satisfy' isLeft
  guard $ (uk ^. name) == keyword


parseWordPostpone = view parseWord' >>= \parseWord -> lift $ parseWord "postpone"
parseWordParens = view parseWord' >>= \parseWord -> lift $ parseWord "("
parseWordExecute = view parseWord' >>= \parseWord -> lift $ parseWord "execute"
parseWordTick = view parseWord' >>= \parseWord -> lift $ parseWord "'"
parseWordLeftBracket = view parseWord' >>= \parseWord -> lift $ parseWord "["
parseWordColon = view parseWord' >>= \parseWord -> lift $ parseWord ":"
parseWordComma = view parseWord' >>= \parseWord -> lift $ parseWord ","
parseWordImmediate = view parseWord' >>= \parseWord -> lift $ parseWord "immediate"
parseWordDo = view parseWord' >>= \parseWord -> lift $ parseWord "do"
parseWordIf = view parseWord' >>= \parseWord -> lift $ parseWord "if"
parseWordCreate = view parseWord' >>= \parseWord -> lift $ parseWord "create"
parseWordDoes = view parseWord' >>= \parseWord -> lift $ parseWord "does>"
parseWordBegin = view parseWord' >>= \parseWord -> lift $ parseWord "begin"
parseWordRepeat = view parseWord' >>= \parseWord -> lift $ parseWord "repeat"
parseWordUntil = view parseWord' >>= \parseWord -> lift $ parseWord "until"
parseWordWhile = view parseWord' >>= \parseWord -> lift $ parseWord "while"


manyWordsTillExcludingWithout :: Te.Text -> [Word] -> ExpressionsM [Node]
manyWordsTillExcludingWithout bs without = withEmpty''' $ do
  parseWord <- view parseWord'
  parseNodeWithout <- view parseNodeWithout'
  expr <- lift $ manyTill (parseNodeWithout without) ((lookAhead (parseWord bs) *> return ()) <|> eof)
  return expr

     
manyWordsTillExcluding :: Te.Text -> ExpressionsM [Node]
manyWordsTillExcluding bs = withEmpty''' $ do
  parseWord <- view parseWord'
  parseNode <- view parseNode'
  expr <- lift $ manyTill parseNode (lookAhead (parseWord bs))
  return expr

manyWordsTillWithout :: Te.Text -> [Word] -> ExpressionsM [Node]
manyWordsTillWithout bs without = do
  parseNodeWithout <- view parseNodeWithout'
  parseWord <- view parseWord'
  let errorMsg = Te.unpack bs
  let parseDelimiter = (parseWord bs <?> errorMsg)
  lift $ withEmpty' $  manyTill (parseNodeWithout without) parseDelimiter
                    

withEmpty' = withEmpty

manyWordsTill :: Te.Text -> ExpressionsM [Node]
manyWordsTill bs  = manyWordsTillWithout bs []

errorHandler handlingFunction colonName = [
                     handler _ClashInWord handlingFunction,
                     handler _BeginUntilNoFlag (handlingFunction . (("The body of begin until must produce a flag value!\n") ++)),
                     handler (_TypeClashM._IfElseExprNotStatic) (handlingFunction . ((colonName <> ": If-Else branches do not have the same type\n") ++) . uncurry (++)),
                     handler_ (_TypeClashM._IfExprNotStatic) (handlingFunction (colonName <> ": An if branch which has an unempty stack effect is not allowed when multiple effects are forbidden")),
                     handler_ _MultiEffs (handlingFunction colonName),
                     handler_ _MultiEffClash (handlingFunction "asdf"),
                     handler_ _CastsNotAllowed (handlingFunction (colonName <> ": Casts are not allowed")),
                     handler _Clash handlingFunction,
                     handler _UnknownWord handlingFunction
                    ]

parseUnknownName :: ExpressionsM String
parseUnknownName = do
  Left uk <- lift $ satisfy' isLeft
  return (uk ^. name)

forbiddenInBranch :: ExpressionsM [Word]
forbiddenInBranch = do
  coreWords <- use wordsMap
  return $ catMaybes $ map (\w -> M.lookup (new _WordIdentifier w) coreWords) ["then", ";", "postpone"]

(</>) = mplus 
