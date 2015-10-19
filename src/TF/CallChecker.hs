module TF.CallChecker where

import Control.Arrow 
import           Control.Error as E
import           Control.Lens hiding (noneOf,(??))
import Lens.Family.Total hiding ((&), Empty)
import           Control.Monad
import           Control.Monad.Writer
import  Text.PrettyPrint (render,vcat, text, ($+$), nest)

import           Control.Monad.RWS
import           TF.Parsers.Parser
import           TF.Parsers.Tokenizer
import           TF.Util
import           TF.CheckerUtils (showCheckerState)
import           TF.Types hiding (word)
import TF.Subtypes
import           Text.Parsec hiding (token)
import TF.Errors
import qualified TF.Printer as P
import qualified Data.Map as M
import qualified Data.Set as S

import System.IO
import System.FilePath

import TF.Type.StackEffect
import TF.Type.Nodes


import TF.Paths
import Data.Tree.Zipper hiding (first,before,after)
import Data.Tree

checkFile :: ParseConfig -> FilePath -> IO ()
checkFile conf file = do
  dir <- getStaticDir
  let filePath =  dir </> file

  handle <- openFile filePath ReadMode
  contents <- hGetContents handle

  runChecker conf contents
  
  hClose handle  
  

runChecker' :: ParseConfig -> String -> (Either Error' ([Node], ParseState), Info)
-- runLoggingT (\loc logsource level logText -> putStrLn logText) . 
runChecker' conf s = do 

     let a :: StackEffectM (Either ParseError ([Node], ParseState))
         a = runProgramParser s

     let b :: StackEffectM (Either Error' ([Node], ParseState))
         b = liftM (E.fmapL (review (_ErrorP._ParseErr') . show)) a
         c :: StackEffectM ([Node], ParseState)
         c = lift . hoistEither =<< b
         -- d :: Script' (([Node], ParseState), ())
         d = evalRWST c conf (CustomState 0 M.empty)
         e :: (Either Error' ([Node], ParseState), Info)
         -- e = return . runIdentity . runWriterT $ runEitherT $ fmap fst $ flip runReaderT conf $ d
         e = runIdentity . runWriterT $ runExceptT $ fmap fst $ d
     e
  where
     runProgramParser :: String -> StackEffectM (Either ParseError ([Node], ParseState))
     runProgramParser s = do
       words' <- parseWords s
       runParserT parseProgram (defParseState & _subtypeRelation .~ subtypeRelation' primitiveTypes (conf ^. subtypes)) "" words'
     -- showInfo :: Info -> IO ()

defParseState :: ParseState
defParseState = ParseState M.empty M.empty INTERPRETSTATE False emptyForthEffect (M.fromList [("object", [])]) (M.fromList [("object", [])]) S.empty M.empty [] (Trace (fromTree $ Node "" []))


         
runChecker :: ParseConfig -> String -> IO ()
runChecker config s = do
    let (res, info) = runChecker' config s
    showInfo info
    res & (_case & on _Error (putStrLn . ("Error: " ++ ) . show)
                 & on _Result showResult

           )
   where
     showResult :: ([Node], ParseState) -> IO ()
     showResult (_, parseState) = do
       let checkerState = showCheckerState parseState
           effs = showEffects' . view (_effects._Wrapped._1) $ parseState
       putStrLn . drawTree . toTree . view (_trace._Wrapped) $ parseState
       putStrLn checkerState
       putStrLn effs
     showInfo :: Info -> IO ()
     showInfo (Info fexprs failures asserts) = do
       let docs = for fexprs $ \fexpr -> nest 0 (P.infoNode fexpr)
           info = text "INFO:" $+$ nest 1 (vcat docs)
           failure = text "FAILURES:" $+$ nest 1 (vcat . map P.checkFailure $ failures)
           assert = text "ASSERT FAILURES:" $+$ nest 1 (vcat . map P.assertFailure $ asserts)
       blockedWith "WRITER:" $ iop . render $ info $+$ failure $+$ assert
       
     renderForthWordsOrExpr = showBoth . first (render . P.pprint) 
     showEffects' :: [(StackEffect, StackEffect)] -> String
     showEffects' = unlines . (:) "\nTOP LEVEL:\n" . map (\(_, execEff) -> render (P.stackEffectWithoutArgs execEff))
     showEffects :: [StackEffect] -> String
     showEffects = unlines . map (render . P.stackEffect)
     showBoth = unlines . toListOf both


  
