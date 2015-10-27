module TF.CallChecker where

import Control.Arrow 
import           Control.Error as E
import           Control.Lens hiding (noneOf,(??))
import Lens.Family.Total hiding ((&), Empty)
import           Control.Monad
import           Control.Monad.Writer
import           Control.Monad.State
import           Control.Monad.Reader
import  Text.PrettyPrint (render,vcat, text, ($+$), nest, Doc)

import           Control.Monad.RWS
import           Control.Monad.Cont
import           TF.Parsers.Parser
import           TF.Parsers.Tokenizer
import           TF.Util
import           TF.Types hiding (word)
import TF.Subtypes
import           Text.Parsec hiding (token)
import TF.Errors
import qualified TF.Printer as P
import qualified Data.Map as M
import qualified Data.Set as S

import System.IO
import System.FilePath
import System.Directory


import TF.Type.StackEffect
import TF.Type.Nodes


import TF.Paths
import Data.Tree.Zipper hiding (first,before,after)
import Data.Tree

checkFile :: ParseConfig -> FilePath -> IO ()
checkFile conf file = (`runContT` return) $ callCC $ \ret -> do
    fileExists <- liftIO $ doesFileExist file
    unless fileExists $ do
      liftIO $ putStrLn $ file <> " does not exist!"
      ret ()
    handle <- liftIO $ openFile file ReadMode
    contents <- liftIO $ hGetContents handle

    liftIO $ runChecker conf contents

    liftIO $ hClose handle  
    return ()

checkStaticFile :: ParseConfig -> FilePath -> IO ()
checkStaticFile conf file = do
  dir <- getStaticDir
  let filePath =  dir </> file

  handle <- openFile filePath ReadMode
  contents <- hGetContents handle

  runChecker conf contents
  
  hClose handle  
  

runChecker' :: ParseConfig -> String -> (((Either Error' ([Node], ParseState)), TreePos Full String), Info)
-- runLoggingT (\loc logsource level logText -> putStrLn logText) . 
runChecker' conf s = do 

     let a :: StackEffectM (Either ParseError ([Node], ParseState))
         a = runProgramParser s

     let b :: StackEffectM (Either Error' ([Node], ParseState))
         b = liftM (E.fmapL (review (_ErrorP._ParseErr') . show)) a
         c :: StackEffectM ([Node], ParseState)
         c = lift . hoistEither =<< b
         d :: ExceptT Error' (StateT CustomState (Writer Info)) ([Node], ParseState)
         d = flip runReaderT conf c 
         e = runIdentity . runWriterT . fmap (second checkedExpressions) . (`runStateT` (CustomState (fromTree (Node "" [])) 0 M.empty)) . runExceptT $ d
     e
  where
     runProgramParser :: String -> StackEffectM (Either ParseError ([Node], ParseState))
     runProgramParser s = do
       words' <- parseWords s
       runParserT parseProgram (defParseState & _subtypeRelation .~ subtypeRelation' primitiveTypes (conf ^. subtypes)) "" words'

defParseState :: ParseState
defParseState = ParseState M.empty M.empty INTERPRETSTATE False emptyForthEffect (M.fromList [("object", [])]) (M.fromList [("object", [])]) S.empty M.empty [] (Trace (fromTree $ Node "" []))

runChecker :: ParseConfig -> String -> IO ()
runChecker config s = do
    let ((res,treeZipper), info) = runChecker' config s
    showInfo info
    putStrLn . render . P.showParseTree . drawTree . toTree $ treeZipper
    case res of
      Left err -> putStrLn $ "Error: " ++ show err
      Right result -> do
        showResult result
   where
     showResult :: ([Node], ParseState) -> IO ()
     showResult (_, parseState) = do
       let checkerState = render $ P.showCheckerState parseState
       putStrLn . render . P.showAST . drawTree . toTree . view (_trace._Wrapped) $ parseState
       putStrLn checkerState
     showInfo :: Info -> IO ()
     showInfo info = putStrLn . render $ P.showInfo info
