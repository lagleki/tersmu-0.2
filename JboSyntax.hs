-- This file is part of tersmu
-- Copyright (C) 2014 Martin Bays <mbays@sdf.org>
--
-- This program is free software: you can redistribute it and/or modify
-- it under the terms of version 3 of the GNU General Public License as
-- published by the Free Software Foundation.
--
-- You should have received a copy of the GNU General Public License
-- along with this program.  If not, see http://www.gnu.org/licenses/.

{-# LANGUAGE DeriveDataTypeable #-}
module JboSyntax where
import Logic hiding (Term, Connective)
import Control.Applicative
import Data.Data
-- Abstract syntax:

data Text = Text {textFrees::[Free], vaguelyNegatedText::Bool,
	textParas::[Paragraph]}
    deriving (Eq, Show, Ord, Typeable, Data)
type Paragraph = [Either Fragment Statement]

data Fragment
    = FragPrenex [Term]
    | FragTerms [Term]
    | FragCon Connective
    | FragQuantifier Mex
    | FragNA Cmavo
    | FragRels [RelClause]
    | FragLinks [Term]
    deriving (Eq, Show, Ord, Typeable, Data)

data Statement = Statement [Free] [Term] Statement1
    deriving (Eq, Show, Ord, Typeable, Data)

data LogJboConnective = LogJboConnective Bool Char Bool
		deriving (Eq, Show, Ord, Typeable, Data)

data Statement1 = ConnectedStatement Connective Statement1 Statement1
		| StatementSentence [Free] Sentence
		| StatementParas (Maybe Tag) [Paragraph]
		deriving (Eq, Show, Ord, Typeable, Data)

data Subsentence = Subsentence [Free] [Term] Sentence
    deriving (Eq, Show, Ord, Typeable, Data)

data Sentence = Sentence [Term] BridiTail
    deriving (Eq, Show, Ord, Typeable, Data)

data Free
    = Bracketed Text
    | Discursive BridiTail
    | TruthQ (Maybe Int)
    | Vocative [COI] (Maybe Sumti)
    | MAI Mex
    | XI Mex
    | MexPrecedence BridiTail
    | SOI Sumti (Maybe Sumti)
    | Indicator {indicatorNai :: Bool, indicatorCmavo :: Cmavo}
    | NullFree
    deriving (Eq, Show, Ord, Typeable, Data)

data COI = COI {coiCOI::String, coiNAI::Bool}
    deriving (Eq, Show, Ord, Typeable, Data)

type FreeIndex = Int

data Term
    = Sumti Tagged Sumti
    | Negation
    | Termset [Term]
    | ConnectedTerms Bool Connective Term Term
    | BareTag Tag
    | BareFA (Maybe Int)
    | NullTerm
    deriving (Eq, Show, Ord, Typeable, Data)

data Tagged = Untagged
	 | Tagged Tag
	 | FATagged Int
	 | FAITagged
	 deriving (Eq, Show, Ord, Typeable, Data)

data AbsTag r t
    = DecoratedTagUnits [DecoratedAbsTagUnit r t]
    | ConnectedTag (AbsConnective r t) (AbsTag r t) (AbsTag r t)
    deriving (Eq, Show, Ord, Typeable, Data)
data DecoratedAbsTagUnit r t = DecoratedTagUnit
    {tagNahe::Maybe Cmavo, tagSE::Maybe Int, tagNAI::Bool, tagUnit::AbsTagUnit r t}
    deriving (Eq, Show, Ord, Typeable, Data)
data AbsTagUnit r t
    = TenseCmavo Cmavo
    | CAhA Cmavo
    | FAhA {fahaHasMohi::Bool, fahaCmavo::Cmavo}
    | ROI {roiroi::Cmavo, roiIsSpace::Bool, roiQuantifier::AbsMex r t}
    | TAhE_ZAhO {taheZoheIsSpace::Bool, taheZahoCmavo::Cmavo}
    | BAI Cmavo
    | FIhO r
    | CUhE
    | KI
    deriving (Eq, Show, Ord, Typeable, Data)

tagNaiIsScalar :: AbsTagUnit r t -> Bool
tagNaiIsScalar (ROI _ _ _) = True
tagNaiIsScalar (TAhE_ZAhO _ _) = True
tagNaiIsScalar (CAhA _) = True
tagNaiIsScalar _ = False

type Tag = AbsTag Selbri Sumti
type DecoratedTagUnit = DecoratedAbsTagUnit Selbri Sumti
type TagUnit = AbsTagUnit Selbri Sumti

data AbsConnective r t
    = JboConnLog (Maybe (AbsTag r t)) LogJboConnective
    | JboConnJoik (Maybe (AbsTag r t)) Joik
    deriving (Eq, Show, Ord, Typeable, Data)
type Connective = AbsConnective Selbri Sumti

type Joik = String

-- XXX we arbitarily consider a mix of tense and "modal" to be a tense
isTense :: AbsTag r t -> Bool
isTense (ConnectedTag _ t1 t2) = isTense t1 || isTense t2
isTense (DecoratedTagUnits dtus) = or $ map isTenseDTU dtus
    where isTenseDTU (DecoratedTagUnit _ _ _ tu) = case tu of
	    BAI _ ->  False
	    FIhO _ -> False
	    _ -> True

type Cmavo = String

data Sumti = ConnectedSumti Bool Connective Sumti Sumti [RelClause]
	   | QAtom [Free] (Maybe Mex) [RelClause] SumtiAtom
	   | QSelbri Mex [RelClause] Selbri
	   deriving (Eq, Show, Ord, Typeable, Data)

appendRelsToSumti newrels (ConnectedSumti fore con s1 s2 rels) =
    ConnectedSumti fore con s1 s2 (rels++newrels)
appendRelsToSumti newrels (QAtom fs q rels sa) =
    QAtom fs q (rels++newrels) sa
appendRelsToSumti newrels (QSelbri q rels s) =
    QSelbri q (rels++newrels) s

data RelClause = Restrictive Subsentence  -- poi
	       | Incidental Subsentence  -- noi
	       | Descriptive Subsentence -- voi
	       | Assignment Term  -- goi
	       | RestrictiveGOI String Term  -- pe etc.
	       | IncidentalGOI String Term  -- ne etc.
	       deriving (Eq, Show, Ord, Typeable, Data)

data SumtiAtom = Name Gadri [RelClause] String
	       | Variable Int -- da
	       | NonAnaphoricProsumti String -- mi
	       | RelVar Int -- ke'a
	       | LambdaVar (Maybe Int) (Maybe Int) -- ce'u [xi ly] [xi ny]
	       | SelbriVar -- fake, for description sumti
	       | Description Gadri (Maybe Sumti) (Maybe Mex) (Either Selbri Sumti) [RelClause] [RelClause]
	       | Assignable Int -- ko'a
	       | LerfuString [Lerfu]
	       | Ri Int -- ri
	       | Ra Cmavo -- ra/ru
	       | MainBridiSumbasti Int -- vo'a
	       | Quote Text
	       | NonJboQuote String
	       | ErrorQuote [String]
	       | Word String
	       | MexLi Mex -- li
	       | MexMex Mex -- mo'e
	       | Zohe -- zo'e
	       | SumtiQ (Maybe Int) -- ma [kau]
	       | QualifiedSumti SumtiQualifier [RelClause] Sumti
	       deriving (Eq, Show, Ord, Typeable, Data)

data Lerfu
    = LerfuChar Char
    | LerfuPA Cmavo
    | LerfuValsi String
    | LerfuShift Cmavo
    | LerfuShifted Cmavo Lerfu
    | LerfuComposite [Lerfu]
    deriving (Eq, Show, Ord, Typeable, Data)

type Gadri = String

getsRi :: SumtiAtom -> Bool
getsRi Zohe = False
getsRi (Assignable _) = False
getsRi (LerfuString _) = False
getsRi (MainBridiSumbasti _) = False
getsRi (Variable _) = False
getsRi (NonAnaphoricProsumti p) = p `elem` ["ti","ta","tu"]
getsRi _ = True

isAssignable :: SumtiAtom -> Bool
isAssignable (Assignable _) = True
isAssignable (LerfuString _) = True
isAssignable (Name _ _ _) = True
isAssignable _ = False

data SumtiQualifier = LAhE String | NAhE_BO String
    deriving (Eq, Show, Ord, Typeable, Data)

data BridiTail = ConnectedBT Connective BridiTail BridiTail [Term]
	       | BridiTail3 Selbri [Term]
	       | GekSentence GekSentence
	       deriving (Eq, Show, Ord, Typeable, Data)

data GekSentence = ConnectedGS Connective Subsentence Subsentence [Term]
		 | TaggedGS Tag GekSentence
		 | NegatedGS GekSentence
		 deriving (Eq, Show, Ord, Typeable, Data)

data Selbri = Negated Selbri
	    | TaggedSelbri Tag Selbri
	    | Selbri2 Selbri2
	    deriving (Eq, Show, Ord, Typeable, Data)

data Selbri2 = SBInverted Selbri3 Selbri2
	     | Selbri3 Selbri3
	     deriving (Eq, Show, Ord, Typeable, Data)

data Selbri3 = SBTanru Selbri3 Selbri3
	     | ConnectedSB Bool Connective Selbri Selbri3
	     | BridiBinding Selbri3 Selbri3
	     | ScalarNegatedSB NAhE Selbri3
	     | TanruUnit [Free] TanruUnit [Term]
	     deriving (Eq, Show, Ord, Typeable, Data)

type NAhE = Cmavo

sb3tosb :: Selbri3 -> Selbri
sb3tosb = Selbri2 . Selbri3

data TanruUnit
    = TUBrivla String
    | TUZei [String]
    | TUBridiQ (Maybe Int)
    | TUGOhA String Int
    | TUMe Sumti
    | TUMoi Sumti String
    | TUAbstraction Abstractor Subsentence
    | TUPermuted Int TanruUnit
    | TUJai (Maybe Tag) TanruUnit
    | TUOperator Operator
    | TUXOhI Tag
    | TUSelbri3 Selbri3
    deriving (Eq, Show, Ord, Typeable, Data)

data Abstractor
    = NU Cmavo
    | NegatedAbstractor Abstractor
    -- Note: tagged connectives aren't allowed with NU, which makes things simpler
    -- (but less uniform...)
    | LogConnectedAbstractor LogJboConnective Abstractor Abstractor
    | JoiConnectedAbstractor Joik Abstractor Abstractor
    deriving (Eq, Show, Ord, Typeable, Data)

data AbsMex r t
    = Operation (AbsOperator r t) [AbsMex r t]
    | ConnectedMex Bool (AbsConnective r t) (AbsMex r t) (AbsMex r t)
    | QualifiedMex SumtiQualifier (AbsMex r t)
    | MexInt Int
    | MexNumeralString [Numeral]
    | MexLerfuString [Lerfu]
    | MexSelbri r
    | MexSumti t
    | MexArray [AbsMex r t]
    deriving (Eq, Show, Ord, Typeable, Data)

type Mex = AbsMex Selbri Sumti

mexIsNumberOrLS (MexInt _) = True
mexIsNumberOrLS (MexNumeralString _) = True
mexIsNumberOrLS (MexLerfuString _) = True
mexIsNumberOrLS _ = False

data Numeral = PA Cmavo | NumeralLerfu Lerfu
    deriving (Eq, Show, Ord, Typeable, Data)

data AbsOperator r t
    = ConnectedOperator Bool (AbsConnective r t) (AbsOperator r t) (AbsOperator r t)
    | OpPermuted Int (AbsOperator r t)
    | OpScalarNegated NAhE (AbsOperator r t)
    | OpMex (AbsMex r t)
    | OpSelbri r
    | OpVUhU Cmavo
    deriving (Eq, Show, Ord, Typeable, Data)

type Operator = AbsOperator Selbri Sumti

lerfuStringsOfSelbri :: Selbri -> [[Lerfu]]
lerfuStringsOfSelbri (Negated sb) = lerfuStringsOfSelbri sb
lerfuStringsOfSelbri (TaggedSelbri _ sb) = lerfuStringsOfSelbri sb
lerfuStringsOfSelbri (Selbri2 sb2) = do
	s <- sb2tols sb2
	[s, take 1 s]
    where
	sb2tols (SBInverted sb3 sb2) = (++) <$> sb3tols sb3 <*> sb2tols sb2
	sb2tols (Selbri3 sb3) = sb3tols sb3
	sb3tols (SBTanru sb sb') = (++) <$> sb3tols sb <*> sb3tols sb'
	sb3tols (ConnectedSB _ _ sb sb3) = (++) <$> sbtols sb <*> sb3tols sb3
	sb3tols (BridiBinding sb3 _) = sb3tols sb3
	sb3tols (TanruUnit _ tu _) = tutols tu
	sbtols = lerfuStringsOfSelbri
	tutols (TUBrivla s) = return $ [LerfuChar $ head s]
	tutols (TUZei vs) = [map (LerfuChar . head) $ vs
	    , [LerfuChar . head . head $ vs]]
	tutols (TUAbstraction (NU s) _) =
	    -- Allow {nu bu} etc as abstraction anaphora.
	    -- Suggested by Michael Turniansky.
	    [[LerfuChar $ head s], [LerfuValsi s]]
	tutols (TUSelbri3 sb3) = sb3tols sb3
	tutols _ = return $ []

{-
class Bifunctor p where
    bimap :: (a -> b) -> (c -> d) -> p a c -> p b d
instance Bifunctor AbsMex where
    bimap fr ft = bimap' where
	bimap' (Operation o ms) = Operation (bimap' o) (map bimap' ms)
	bimap' (ConnectedMex f c m1 m2) = ConnectedMex f (bimap' c) (bimap' m1) (bimap' m2)
	bimap' (QualifiedMex q m) = QualifiedMex q (bimap' m)
	bimap' (MexArray ms) = MexArray $ map bimap' ms
	bimap' (MexSelbri r) = MexSelbri $ fr r
	bimap' (MexSumti t) = MexSumti $ ft t
	bimap' x = x
    
instance Bifunctor AbsOperator where
    bimap fr ft = bimap' where
	bimap' (ConnectedOperator f c o1 o2) = ConnectedOperator f (bimap' c) (bimap' o1) (bimap' o2)
	bimap' (OpPermuted s o) = OpPermuted s $ bimap' o
	bimap' (OpScalarNegated n o) = OpScalarNegated n $ bimap' o
	bimap' (OpMex m) = OpMex $ bimap' m
	bimap' (OpSelbri r) = OpSelbri $ fr r
	bimap' x = x
-}
