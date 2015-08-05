-- This file is part of tersmu
-- Copyright (C) 2014 Martin Bays <mbays@sdf.org>
--
-- This program is free software: you can redistribute it and/or modify
-- it under the terms of version 3 of the GNU General Public License as
-- published by the Free Software Foundation.
--
-- You should have received a copy of the GNU General Public License
-- along with this program.  If not, see http://www.gnu.org/licenses/.

module ParseText (parseText) where

import Lojban
import Pappy.Pos
import Pappy.Parse
import JboSyntax

import Control.Applicative
-- import Debug.Trace
-- traceIt x = traceShow x x

parseText :: String -> Either Int Text
parseText str = nudgeFrees (lojbanterminatedText . lojbanParse "terminatedText") $ str ++ " %%%END%%%"

afterPos :: Pos -> String -> String
afterPos p s = drop (posCol p - 1) s

-- |nudgeFrees: move indicators and frees backwards until they're in one of
-- the prescribed positions where our main grammar can parse them (basically:
-- after a term, or at the start of a sentence or similar construct).
-- Works as follows: try to parse; if fail, try to parse a free at fail point,
-- recursively nudging frees to do so; if find such a misplaced free, move it
-- back a word and try parsing again.
-- Rather a hack, obviously, but it seems to work!
--
-- FIXME: MAI isn't really handled, since the parse failure can come at the
-- MAI rather than the start of the free, so e.g. "za'u re'u re mai broda"
-- fails. Similarly {le zarci e re mai le zdani}
--
-- FIXME: {li ci xi pa su'i vo} - nudging the xi clause back has it pick up
-- the {ci}, resulting in a parse error. Can be fixed by bracketing our free
-- before nudging it.
--
-- FIXME: more seriously, this appraoch doesn't actually work - the parse
-- error caused by a misplaced free often isn't at the start of the free, for
-- various reasons. Probably we should consider the current algorithm "good
-- enough for present purposes", but plan to move to piggy-backing on a full
-- camxes implementation. For example, we could literally depend on the
-- standard camxes java implementation, parse its output to find frees and
-- move them into canonical positions, then put them through this parser -
-- with the hacky preparsing implemented in this file as a fallback when we
-- don't have access to camxes.
--
-- Note: probably makes more sense to have our canonical free positions be
-- after QAtom and TanruUnit and at (sub)sentence start, rather than riding on
-- Term as at present.
--
-- XXX: possible source of parse bugs: misplaced free can interrupt crucial
-- greed. e.g. "tag sumti / tag KU?" acts buggily on "vi ue ta",
-- and has to be "tag sumti / tag !free KU". I think I've got all those now,
-- but may be wrong.
--
-- TODO: optimise; currently we're doing string manipulation with String,
-- which is a bad idea, and more to the point we're reparsing the whole text
-- repeatedly. Chunking the text into paragraphs would be a start.
--
nudgeFrees :: (String -> Result LojbanDerivs a) -> String -> Either Int a
nudgeFrees parse s = fmap fst $ nudgeFrees' False parse s where
    nudgeFrees' :: Bool -> (String -> Result LojbanDerivs a) -> String -> Either Int (a,Int)
    nudgeFrees' inFree parse str =
	case parse str of
	    Parsed a d _ -> Right (a, parsedPoint d)
	    NoParse e ->
		let pos = errorPoint e
		    (head,tail) = splitAt pos str
		in if inFree && pos == 0 then Left 0
		else case nudgeFrees' True parseFree tail of
		    Left n -> Left $ pos + n
		    Right (_,flen) ->
			nudgeFrees' inFree parse $ nudgeFree head tail flen
    errorPoint e = posCol (errorPos e) - 1
    parsedPoint d = posCol (dvPos d) - 1
    parseFree = lojbanfree . lojbanParse "free"
    nudgeFree head tail flen =
	let ws = words head
	    (headws',headws'') = splitAt (length ws - 1) ws
	    (free,tail') = splitAt flen tail
	in unwords headws' ++ (if null headws' then "" else " ") ++
	    free ++ unwords headws'' ++ " " ++ tail'

{-
-- Direct parsing without any preprocessing - currently unused
parseAText :: String -> Either Int [Statement]
parseAText str = case lojbanatext1 (lojbanParse "atext1" (str ++ " ")) of
	Parsed p _ _ -> Right p
	NoParse e -> Left (posCol (errorPos e))

-- |parseTextSplitting: split text into statements, strip indicators&free from each,
-- and parse the stripped statements. Unused.
-- Doesn't handle fragments, nor the 'text' production in full detail.
parseTextSplitting :: String -> [ Either (String,Int) (Statement,[Free]) ]
parseTextSplitting = parseText' . stripTextHead . (++" ") where
    parseText' str = case parseStatement str of
	    Left n -> [Left (str,n)]
	    Right (parsed,tail) -> if null tail
		then [Right parsed]
		else Right parsed:parseText' tail
    parseStatement :: String -> Either Int ((Statement,[Free]),String)
    parseStatement = stripFrees $ lojbanwholeStatement . lojbanParse "wholeStatement"
    stripTextHead :: String -> String
    stripTextHead str =
	let Parsed _ d _ = lojbantextHead . lojbanParse "textHead" $ str
	in afterPos (dvPos d) str
-}
