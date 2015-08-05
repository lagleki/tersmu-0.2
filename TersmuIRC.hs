-- This file is part of tersmu
-- Copyright (C) 2014 Martin Bays <mbays@sdf.org>
--
-- This program is free software: you can redistribute it and/or modify
-- it under the terms of version 3 of the GNU General Public License as
-- published by the Free Software Foundation.
--
-- You should have received a copy of the GNU General Public License
-- along with this program.  If not, see http://www.gnu.org/licenses/.

module TersmuIRC (onelineParse) where

import ParseText (parseText)
import JboParse (evalText, evalStatement)
import JboSyntax
import ParseM (ParseStateM, evalParseStateM)
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

onelineParse :: Bool -> String -> String
onelineParse jbo s =
    case morph s of
        Left errpos ->
            "Morphology error at " ++ show errpos
        Right text ->
            evalParseStateM $ showParsedText jbo text $ parseText text

showParsedText :: Bool -> String -> Either Int Text -> ParseStateM String
showParsedText jbo s (Right text) = do
    jboText <- mapStateT (return.runIdentity) $ JboParse.evalText text
    return $ onelinify jbo $ evalBindful $ logjboshow jbo jboText
showParsedText jbo s (Left pos) = return $ "Parse error at " ++ show pos

onelinify :: Bool -> String -> String
onelinify jbo "" = ""
onelinify jbo ('\n':cs) = (if jbo then " " else ";  ") ++ onelinify jbo cs
onelinify jbo (c:cs) = c:onelinify jbo cs
