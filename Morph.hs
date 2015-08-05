-- This file is part of tersmu
-- Copyright (C) 2014 Martin Bays <mbays@sdf.org>
--
-- This program is free software: you can redistribute it and/or modify
-- it under the terms of version 3 of the GNU General Public License as
-- published by the Free Software Foundation.
--
-- You should have received a copy of the GNU General Public License
-- along with this program.  If not, see http://www.gnu.org/licenses/.

module Morph (morph) where
import Morphology
import Pappy.Pos
import Pappy.Parse
import Data.Char

morph :: String -> Either Int String
morph s = let
        Parsed words d _ = morphologywords $ morphologyParse "words" $ stripPunc s ++ " "
        p = posCol (dvPos d) - 1
    in if p < length s
        then Left p
        else Right $ map toLower $ unwords $ words

stripPunc :: String -> String
stripPunc =
    -- TODO: shouldn't strip inside zoi quotes
    -- (but shouldn't allow "%%%END%%%" in them either...)
    map $ \c -> if isAlphaNum c || isSpace c || c `elem` ",'" then c else ' '
