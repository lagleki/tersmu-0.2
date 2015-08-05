-- This file is part of tersmu
-- Copyright (C) 2014 Martin Bays <mbays@sdf.org>
--
-- This program is free software: you can redistribute it and/or modify
-- it under the terms of version 3 of the GNU General Public License as
-- published by the Free Software Foundation.
--
-- You should have received a copy of the GNU General Public License
-- along with this program.  If not, see http://www.gnu.org/licenses/.

{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, DeriveDataTypeable #-}
module JboProp where

import Logic hiding (Term)
import qualified Logic (Term)
import JboSyntax

import Bindful

import Data.Maybe
import Control.Applicative
import Data.Foldable (traverse_, Foldable, sequenceA_)
import Control.Monad.Writer
import Data.Data
import Data.Generics.Schemes

type JboProp = Prop JboRel JboTerm Joik JboModalOp JboQuantifier

data JboTerm = BoundVar Int
	     | Var Int
	     | Constant Int [JboTerm]
	     | Named String
	     | PredNamed JboPred
	     | NonAnaph String
	     | UnboundSumbasti SumtiAtom
	     | JboQuote ParsedQuote
	     | JboErrorQuote [String]
	     | JboNonJboQuote String
	     | TheMex Mex -- me'o
	     | Value JboMex -- li
	     | Valsi String
	     | Unfilled
	     | JoikedTerms Joik JboTerm JboTerm
	     | QualifiedTerm SumtiQualifier JboTerm
	     deriving (Eq, Show, Ord, Typeable, Data)

data JboRel = Tanru JboVPred JboRel
	    | TanruConnective JboConnective JboVPred JboVPred
	    | ScalarNegatedRel NAhE JboRel
	    | AbsPred Abstractor JboNPred
	    | AbsProp Abstractor JboProp
	    | Moi JboTerm Cmavo
	    | Among JboTerm
	    | Equal
	    | UnboundBribasti TanruUnit
	    | BoundRVar Int
	    | RVar Int
	    | OperatorRel JboOperator
	    | TagRel JboTag -- xo'i
	    | Brivla String
    deriving (Eq, Show, Ord, Typeable, Data)

data JboModalOp
    = JboTagged JboTag (Maybe JboTerm)
    | WithEventAs JboTerm
    | QTruthModal
    | NonVeridical
    deriving (Eq, Show, Ord, Typeable, Data)
type JboTag = AbsTag JboVPred JboTerm
type JboDecoratedTagUnit = DecoratedAbsTagUnit JboVPred JboTerm
type JboTagUnit = AbsTagUnit JboVPred JboTerm
type JboConnective = AbsConnective JboVPred JboTerm

-- variadic, n-ary, and unary predicates
type JboVPred = [JboTerm] -> JboProp
data JboNPred = JboNPred Int ([JboTerm] -> JboProp)
    deriving (Typeable,Data)
type JboPred = JboTerm -> JboProp
vPredToPred vp o = vp [o]
predToNPred p = JboNPred 1 (\(o:_) -> p o)

instance Dummyful JboTerm where dummy = Unfilled
instance Dummyful [JboTerm] where dummy = []

jboPredToLojPred :: JboPred -> (Int -> JboProp)
jboPredToLojPred r = \v -> r (BoundVar v)

type JboMex = AbsMex JboVPred JboTerm
type JboOperator = AbsOperator JboVPred JboTerm

data JboQuantifier
    = MexQuantifier JboMex
    | LojQuantifier LojQuantifier
    | QuestionQuantifier
    | RelQuantifier JboQuantifier
    deriving (Eq, Show, Ord, Typeable, Data)

instance Logic.Term JboTerm where
    var n = BoundVar n

data JboFragment
    = JboFragTerms [JboTerm]
    | JboFragUnparsed Fragment
    deriving (Eq, Show, Ord, Typeable, Data)

type JboText = [Texticule]
data Texticule
    = TexticuleFrag JboFragment
    | TexticuleProp JboProp
    deriving (Eq, Show, Ord, Typeable, Data)
propTexticules :: [Texticule] -> [JboProp]
propTexticules [] = []
propTexticules (TexticuleProp p:ts) = p:propTexticules ts
propTexticules (_:ts) = propTexticules ts

-- |ParsedQuote: using this newtype so we can provide dummy instances for use
-- in derived instances for JboTerm
newtype ParsedQuote = ParsedQuote JboText
    deriving (Typeable,Data)
instance Eq ParsedQuote where x == y = False
instance Show ParsedQuote where show q = "<< ... >>"
instance Ord ParsedQuote where x <= y = False

-- can't derive instances for props, since we handle quantifiers with
-- functions, so we define these dummy ones to allow derivations for other
-- types
instance Eq JboProp where { _ == _ = False }
instance Show JboProp where { show _ = "[ ... ]" }
instance Ord JboProp where { _ <= _ = False }
instance Eq JboPred where { _ == _ = False }
instance Show JboPred where { show _ = "[ \\_ -> ... ]" }
instance Ord JboPred where { _ <= _ = False }
instance Eq JboVPred where { _ == _ = False }
instance Show JboVPred where { show _ = "[ \\[_] -> ... ]" }
instance Ord JboVPred where { _ <= _ = False }
instance Eq JboNPred where { _ == _ = False }
instance Show JboNPred where { show (JboNPred n _) = "[ \\_1,...,\\_"++show n++" -> ... ]" }
instance Ord JboNPred where { _ <= _ = False }

-- XXX: hairy generic programming below; to handle our function types, for
-- which we can't just derive Data instances, we use a mixture of dummy Data
-- instances and special case-by-case handling
gsubstituteIn :: (Eq a, Data a, Data b) => a -> a -> b -> b
gsubstituteIn s t x = case cast x of
    Just s' | s' == s -> fromJust $ cast t 
    _ -> case (cast x :: Maybe (JboTerm -> JboProp)) of
	Just pred -> fromJust $ cast $ gsubstituteIn s t . pred
	_ -> case (cast x :: Maybe (Int -> JboProp)) of
	    Just pred -> fromJust $ cast $ gsubstituteIn s t . pred
	    _ -> case (cast x :: Maybe ([JboTerm] -> JboProp)) of
		Just pred -> fromJust $ cast $ gsubstituteIn s t . pred
		_ -> gmapT (gsubstituteIn s t) x
subTerm :: JboTerm -> JboTerm -> JboProp -> JboProp
subTerm = gsubstituteIn
subRel :: JboRel -> JboRel -> JboProp -> JboProp
subRel = gsubstituteIn
gtraverse_ :: (Data a, Data b, Applicative f) => (a -> f ()) -> b -> f ()
gtraverse_ f x = case cast x of
	Just a -> f a
	_ -> case cast x of
	    Just (JboNPred arity pred) -> gtraverse_ f $ pred $ replicate arity Unfilled
	    _ -> sequenceA_ $ gmapQ (gtraverse_ f) x

freeVars :: JboProp -> [JboTerm]
freeVars p = execWriter $ collectFrees p where
	collectFrees = gtraverse_ collectFreesInTerm
	collectFreesInTerm free@(Var _) = tell $ [free]
	collectFreesInTerm free@(UnboundSumbasti (MainBridiSumbasti _)) = tell $ [free]
	collectFreesInTerm (JoikedTerms joik t1 t2) = collectFreesInTerm t1 *> collectFreesInTerm t2
	collectFreesInTerm (QualifiedTerm qual t) = collectFreesInTerm t
	collectFreesInTerm (Constant _ ts) = traverse_ collectFreesInTerm ts
	collectFreesInTerm (Value m) = gtraverse_ collectFreesInTerm m
	collectFreesInTerm (PredNamed p) = gtraverse_ collectFreesInTerm p
	collectFreesInTerm _ = pure ()

connToFOL :: LogJboConnective -> JboProp -> JboProp -> JboProp
connToFOL (LogJboConnective True 'e' True) p1 p2 = Connected And p1 p2
connToFOL (LogJboConnective True 'a' True) p1 p2 = Connected Or p1 p2
connToFOL (LogJboConnective False 'a' True) p1 p2 = Connected Impl p1 p2
connToFOL (LogJboConnective True 'a' False) p1 p2 = Connected Impl p2 p1
connToFOL (LogJboConnective True 'o' True) p1 p2 = Connected Equiv p1 p2
connToFOL (LogJboConnective True 'u' True) p1 p2 = p1
connToFOL (LogJboConnective True 'U' True) p1 p2 = p2
connToFOL (LogJboConnective False c b2) p1 p2 =
    connToFOL (LogJboConnective True c b2) (Not p1) p2
connToFOL (LogJboConnective b1 c False) p1 p2 =
    connToFOL (LogJboConnective b1 c True) p1 (Not p2)

joikToFOL :: Joik -> JboProp -> JboProp -> JboProp
joikToFOL joik = NonLogConnected joik

andPred :: [JboPred] -> JboPred
andPred ps x = bigAnd [p x | p <- ps]

andMPred :: [JboPred] -> Maybe JboPred
andMPred [] = Nothing
andMPred ps = Just $ andPred ps

isAmong :: JboTerm -> (JboTerm -> JboProp)
isAmong y = \o -> Rel (Among y) [o]
