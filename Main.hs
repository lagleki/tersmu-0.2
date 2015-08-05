-- This file is part of tersmu
-- Copyright (C) 2014 Martin Bays <mbays@sdf.org>
--
-- This program is free software: you can redistribute it and/or modify
-- it under the terms of version 3 of the GNU General Public License as
-- published by the Free Software Foundation.
--
-- You should have received a copy of the GNU General Public License
-- along with this program.  If not, see http://www.gnu.org/licenses/.

module Main where

import ParseText (parseText)
import JboParse (evalText, evalStatement)
import JboSyntax
import ParseM (ParseStateT, evalParseStateT)
import JboShow
import Logic
import Bindful
import Morph

import Control.Monad.State
import Control.Monad.Identity
import Control.Applicative
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List
import Data.Char
import Data.Either
import System.IO
import System.IO.Error
import System.Exit
import System.Process
import System.Environment
import System.Console.GetOpt

versionString = "0.2"

doParse :: OutputType -> Handle -> Handle -> String -> IO ()
doParse ot h herr s = case morph s of
    Left errpos -> highlightError herr errpos s "Morphology error"
    Right text -> evalParseStateT $ showParsedText ot h herr text $ parseText text

showParsedText :: OutputType -> Handle -> Handle -> String -> Either Int Text -> ParseStateT IO ()
showParsedText ot h _ s (Right text) = do
    jboText <- mapStateT (return.runIdentity) $ JboParse.evalText text
    when (not $ null jboText) $ do
        liftIO $ hPutStr h $ concat
	    [if not $ (jbo && ot == Loj) || (not jbo && ot == Jbo)
		then evalBindful (logjboshow jbo jboText) ++ "\n\n"
		else ""
	    | jbo <- [False,True]
	    ]
showParsedText _ _ herr s (Left pos) = highlightError herr pos s "Parse error"

highlightError h pos s errstr = let context = 40 in
    liftIO $ hPutStr h $ errstr++":" ++
	"\n\t{" ++ take (context*2) (drop (pos-context) s) ++ "}" ++
	"\n\t " ++ replicate (min pos context) ' ' ++
	"^" ++
	"\n\n"

data OutputType = Jbo | Loj | Both
    deriving (Eq, Ord, Show)
data InputType = WholeText | Paras | Lines
    deriving (Eq, Ord, Show)
data Opt = Output OutputType | Input InputType | Help | Version
    deriving (Eq, Ord, Show)
options =
    [ Option ['l'] ["loj"] (NoArg (Output Loj)) "output logical form only"
    , Option ['j'] ["jbo"] (NoArg (Output Jbo)) "output forethoughtful lojbanic form only"
    , Option ['L'] ["lines"] (NoArg (Input Lines)) "interpret each line as a lojban text"
    , Option ['p'] ["paragraphs"] (NoArg (Input Paras)) "interpret each blank-line-separated paragraph as a lojban text"
    , Option ['v'] ["version"] (NoArg Version) "show version"
    , Option ['h'] ["help"] (NoArg Help) "show help"
    ]
parseArgs :: [String] -> IO ([Opt],[String])
parseArgs argv =
    case getOpt Permute options argv of
	(o,_,[]) | Help `elem` o -> putStrLn (usageInfo header options) >> exitWith ExitSuccess
	(o,_,[]) | Version `elem` o -> putStrLn versionString >> exitWith ExitSuccess
	(o,n,[]) -> return (o,n)
	(_,_,errs) -> ioError (userError (concat errs ++ usageInfo header options))
    where header = "Usage: tersmu [OPTION...] [in] [out]\n\t(use '-' for stdin/stdout)"
main :: IO ()
main = do
    (opts,args) <- getArgs >>= parseArgs
    let outType = last $ Both:[t | Output t <- opts]
    let inType = last $ WholeText:[t | Input t <- opts]
    (inf, h) <- case args of
	[] -> return (Nothing,stdout)
	[infn] -> do
	    s <- if infn == "-" then getContents else readFile infn
	    return (Just s,stdout)
	[infn,outfn] -> do
	    s <- if infn == "-" then getContents else readFile infn
	    h <- if outfn == "-" then return stdout else openFile outfn WriteMode
	    return (Just s, h)
    case inf of
	Nothing -> repl outType h `catchIOError` (\e ->
	    if isEOFError e then exitWith ExitSuccess
		else putStr (show e) >> exitFailure)
	Just s -> mapM (doParse outType h stderr) (mangleInput inType s) >> hClose h
    where
	repl outType h = do
	    -- interactive mode
	    hPutStr stderr "> "
	    hFlush stderr
	    s <- getLine
	    hPutStrLn stderr ""
	    doParse outType h stderr s
	    repl outType h
	mangleInput WholeText = (\x -> [x]) . map (\c -> if c `elem` "\n\r" then ' ' else c)
	mangleInput Lines = lines
	mangleInput Paras = map (intercalate " ") . splitAtNulls . lines
	splitAtNulls ls = let (h,t) = break null ls in
	    h : if null t then [] else splitAtNulls (tail t)
