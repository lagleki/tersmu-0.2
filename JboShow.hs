-- This file is part of tersmu
-- Copyright (C) 2014 Martin Bays <mbays@sdf.org>
--
-- This program is free software: you can redistribute it and/or modify
-- it under the terms of version 3 of the GNU General Public License as
-- published by the Free Software Foundation.
--
-- You should have received a copy of the GNU General Public License
-- along with this program.  If not, see http://www.gnu.org/licenses/.

{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module JboShow where

import Bindful
import JboSyntax
import JboProp
import Logic hiding (Term)
import Util

import Data.Maybe
import Control.Applicative
import Data.Traversable (traverse)
import Data.List

---- Printing routines, in lojban and in (customized) logical notation
-- XXX: output liable to change in future versions. Please do not rely on it.

instance Rel JboRel where
    relstr r = evalBindful $ logshow r

data ShowBindable
    = SVar Int
    | SRVar Int
    | SAss Int
    | SRAss Int
    | SRel Int
    | SLambda Int Int
    deriving (Eq, Show, Ord)

class JboShow t where
    jboshow :: t -> Bindful ShowBindable String
    logshow :: t -> Bindful ShowBindable String
    logjboshow :: Bool -> t -> Bindful ShowBindable String

    -- minimal complete definition: (jboshow and logshow) or logjboshow
    jboshow = logjboshow True
    logshow = logjboshow False
    logjboshow jbo = if jbo then jboshow else logshow

withNext :: (Int -> ShowBindable) -> (Int -> Bindful ShowBindable a) -> (Bindful ShowBindable a)
withNext v f = do
    vals <- getValues
    let n = head [ n | n <- [1..], not $ (v n) `elem` vals ]
    withBinding (v n) f

withShuntedRelVar f =
    do twiddleBound $ \s -> case s of SRel n -> SRel $ n+1
				      _ -> s
       r <- withBinding (SRel 1) f
       twiddleBound $ \s -> case s of SRel n -> SRel $ n-1
				      _ -> s
       return r
withShuntedLambdas arity f = do
    twiddleBound $ \s -> case s of
	SLambda l n -> SLambda (l+1) n
	_ -> s
    r <- ($[]) $ foldl (\h b -> \ns -> b $ \n -> h $ n:ns)
	f [withBinding (SLambda 1 n) | n <- [1..arity]]
    twiddleBound $ \s -> case s of
	SLambda l n -> SLambda (l-1) n
	_ -> s
    return r

bracket :: Char -> String -> String
bracket c =
    let end = case c of
	    '(' -> ")"
	    '[' -> "]"
	    '{' -> "}"
	    '<' -> ">"
	    '"' -> "\""
	    '\'' -> "\'"
	    ' ' -> " "
	    _ -> ""
    in (c:) . (++end)
brackets :: String -> String -> String
brackets bs s = foldr bracket s bs

jbobracket :: String -> String -> String -> String
jbobracket l r = ((l++" ")++) . (++(" "++r))

instance JboShow String where
    logjboshow _ s = return s

instance JboShow JboQuantifier where
    logjboshow _ QuestionQuantifier = return "?"
    logjboshow jbo (LojQuantifier q) = logjboshow jbo q
    logjboshow jbo (MexQuantifier m) = logjboshow jbo m
instance JboShow LojQuantifier where
    jboshow Exists = return "su'o"
    jboshow Forall = return "ro"
    jboshow (Exactly n) = return $ jbonum n
    logshow = return . show

logjboshowlist :: JboShow a => Bool -> [a] -> Bindful ShowBindable String
logjboshowlist jbo as = do
    ass <- mapM (logjboshow jbo) as
    return $ intercalate (if jbo then " " else ",") ass 

instance JboShow Mex where
    logjboshow _ m = return $ show m
instance JboShow JboMex where
    logjboshow jbo (Operation op ms) = do
	ops <- logjboshow jbo op
	mss <- logjboshowlist jbo ms
	return $ if jbo
	    then "pe'o "++ops++" "++mss++" ku'e"
	    else ops++"("++mss++")"
    logjboshow jbo (ConnectedMex fore con m m') = do
	[ms,ms'] <- mapM (logjboshow jbo) [m,m']
	cs <- logjboshowConn jbo "." con
	if jbo
	    then return $ "vei " ++ ms ++" ve'o " ++ cs ++ " vei " ++ ms' ++ " ve'o"
	    else return $ "(" ++ ms ++ ")" ++ cs ++ "(" ++ ms' ++ ")"
    logjboshow jbo (QualifiedMex qual t) = do
	ts <- logjboshow jbo t
	let quals = case qual of {LAhE l -> l; NAhE_BO n -> n ++ " bo"}
	return $ if jbo
	    then quals ++ " " ++ ts ++ " lu'u"
	    else "{" ++ quals ++ "}(" ++ ts ++ ")"
    logjboshow jbo@True (MexInt n) = (++" boi") <$> logjboshow jbo n
    logjboshow jbo@False (MexInt n) = logjboshow jbo n
    logjboshow jbo@True (MexNumeralString ns) = (++" boi") <$> logjboshowlist jbo ns
    logjboshow jbo@False (MexNumeralString ns) = bracket '(' <$> logjboshowlist True ns
    logjboshow jbo@True (MexLerfuString ls) = (++" boi") <$> logjboshow jbo ls
    logjboshow jbo@False (MexLerfuString ls) = bracket '(' <$> logjboshow True ls
    logjboshow jbo@False (MexSelbri p) = bracket '[' <$> logjboshow jbo p
    logjboshow jbo@True (MexSelbri p) = jbobracket "ni'e" "te'u" <$> logjboshow jbo p
    logjboshow jbo@False (MexSumti t) = bracket '[' <$> logjboshow jbo t
    logjboshow jbo@True (MexSumti t) = jbobracket "mo'e" "te'u" <$> logjboshow jbo t
    logjboshow jbo@False (MexArray ms) = bracket '[' <$> logjboshowlist jbo ms
    logjboshow jbo@True (MexArray ms) = jbobracket "jo'i" "te'u" <$> logjboshowlist jbo ms

-- |logjboshownumber: for cases when we shouldn't append a {boi} (number and
-- numberOrLerfuString productions)
logjboshownumber :: Bool -> JboMex -> Bindful ShowBindable String
logjboshownumber _ m | not (mexIsNumberOrLS m) = error "[BUG: Full mex in ljsn]"
logjboshownumber jbo (MexInt n) = logjboshow jbo n
logjboshownumber jbo@True (MexNumeralString ns) = logjboshowlist jbo ns
logjboshownumber jbo@False (MexNumeralString ns) = bracket '(' <$> logjboshowlist True ns
logjboshownumber jbo@True (MexLerfuString ls) = logjboshow jbo ls
logjboshownumber jbo@False (MexLerfuString ls) = bracket '(' <$> logjboshow True ls

instance JboShow Numeral where
    logjboshow True (PA pa) = return pa
    logjboshow False (PA pa) = return $ "{" ++ pa ++ "}"
    logjboshow jbo (NumeralLerfu l) = logjboshow jbo l

instance JboShow [Lerfu] where
    logjboshow jbo ls =
	intercalate (if jbo then " " else "") <$> mapM (logjboshow jbo) ls
instance JboShow Lerfu where
    logjboshow True (LerfuChar c) = return $ case c of
	_ | c `elem` "aoeui" -> (c:"bu")
	'y' -> "y bu"
	'h' -> "y'y"
	_ | c `elem` ['0'..'9'] -> jbonum $ fromEnum c - fromEnum '0'
	_ -> c:"y"
    logjboshow False (LerfuChar c) = return $ [c]
    logjboshow jbo (LerfuPA p) = return $ (if jbo then id else bracket '{') p
    logjboshow jbo (LerfuValsi v) = return $ (if jbo then (++" bu") else bracket '{') v
    logjboshow jbo (LerfuShift s) =
	return $ (if jbo then id else bracket '{') s
    logjboshow jbo (LerfuShifted lau l) =
	(if jbo then ((lau++" ")++) else ((bracket '{' lau)++) . bracket '(') <$> 
	    logjboshow jbo l
    logjboshow jbo (LerfuComposite ls) =
	(if jbo then jbobracket "tei" "foi" else bracket '[') <$>
	    logjboshowlist jbo ls
instance JboShow JboOperator where
    logjboshow jbo (ConnectedOperator _ con op op') = do
	[ops,ops'] <- mapM (logjboshow jbo) [op,op']
	cs <- logjboshowConn jbo "j" con
	if jbo
	    then return $ "ke " ++ ops ++ " ke'e " ++ cs ++ " ke " ++ ops' ++ " ke'e"
	    else return $ "<" ++ ops ++ ">" ++ cs ++ "<" ++ ops' ++ ">"
    logjboshow jbo (OpPermuted s o) =
	((seToStr s ++ " ") ++) <$> logjboshow jbo o
    logjboshow jbo (OpScalarNegated n op) = do
	ops <- logjboshow jbo op
	return $ if jbo then n ++ " " ++ ops else "{"++n++"}("++ops++")"
    logjboshow jbo@False (OpMex m) = bracket '[' <$> logjboshow jbo m
    logjboshow jbo@True (OpMex m) = jbobracket "ma'o" "te'u" <$> logjboshow jbo m
    logjboshow jbo@False (OpSelbri s) = bracket '[' <$> logjboshow jbo s
    logjboshow jbo@True (OpSelbri s) = jbobracket "na'u" "te'u" <$> logjboshow jbo s
    logjboshow jbo@False (OpVUhU v) = bracket '{' <$> return v
    logjboshow jbo@True (OpVUhU v) = return v

logjboshowLogConn _ prefix (LogJboConnective b c b') =
	return $ (if not b then "na " else "") ++
	    prefix ++ [c] ++
	    if not b' then " nai" else ""

logjboshowConn False prefix con = do
    js <- logjboshowConn True prefix con
    return $ "{"++js++"}"
logjboshowConn True prefix (JboConnLog mtag lcon) = do
    lc <- logjboshowLogConn True prefix lcon
    mtags <- maybe "" ((" "++).(++" bo")) <$> traverse (logjboshow True) mtag
    return $ lc ++ mtags
logjboshowConn True prefix (JboConnJoik mtag joik) = do
    let jois = if joik == "??" then case prefix of
		"." -> "ji"
		"j" -> "je'i"
		_ -> "BUG"
	    else joik
    mtags <- maybe "" ((" "++).(++" bo")) <$> traverse (logjboshow True) mtag
    return $ jois ++ mtags

instance JboShow JboTag where
    logjboshow jbo (ConnectedTag con tag1 tag2) = do
	[s1,s2] <- mapM (logjboshow jbo) [tag1,tag2]
	conns <- logjboshowConn jbo "j" con
	return $ if jbo
	    then s1 ++ " " ++ conns ++ " " ++ s2
	    else conns ++ "(" ++ s1 ++ "," ++ s2 ++ ")"
    logjboshow jbo (DecoratedTagUnits dtus) =
	(intercalate " " <$>) $ (`mapM` dtus)
	$ \(DecoratedTagUnit nahe se nai tu) -> do
	    tus <- logjboshow jbo tu
	    return $ maybe "" (++" ") nahe
		++ maybe "" ((++" ").seToStr) se
		++ tus
		++ if nai then " nai" else ""
instance JboShow JboTagUnit where
    logjboshow jbo (TenseCmavo s) = return s
    logjboshow jbo (CAhA s) = return s
    logjboshow jbo (BAI s) = return s
    logjboshow jbo (FAhA mohi s) = return $
	(if mohi then "mo'i " else "") ++ s
    logjboshow jbo (ROI r fehe q) = do
	qs <- logjboshownumber jbo q
	return $ 
	    (if fehe then "fe'e " else "") ++ qs ++ " " ++ r
    logjboshow jbo (TAhE_ZAhO fehe s) = return $
	(if fehe then "fe'e " else "") ++ s
    logjboshow jbo (FIhO p) = do
	ps <- logjboshow jbo p
	return $ "fi'o " ++ ps ++ if jbo then " fe'u" else ""
    logjboshow jbo KI = return "ki"
    logjboshow jbo CUhE = return "cu'e"

instance JboShow Abstractor where
    logjboshow _ (NU n) = return n
    logjboshow jbo (NegatedAbstractor a) = (++"nai") <$> logjboshow jbo a
    logjboshow jbo (LogConnectedAbstractor con a1 a2) = do
	[s1,s2] <- mapM (logjboshow jbo) [a1,a2]
	conns <- logjboshowLogConn jbo "j" con
	return $ if jbo
	    then s1 ++ " " ++ conns ++ " " ++ s2
	    else "({" ++ conns ++ "}(" ++ s1 ++ "," ++ s2 ++ "))"
    logjboshow jbo (JoiConnectedAbstractor joik a1 a2) = do
	[s1,s2] <- mapM (logjboshow jbo) [a1,a2]
	conns <- logjboshow jbo joik
	return $ if jbo
	    then s1 ++ " " ++ conns ++ " " ++ s2
	    else "({" ++ conns ++ "}(" ++ s1 ++ "," ++ s2 ++ "))"

instance JboShow JboPred where
    logjboshow jbo p = logjboshowpred jbo (\n -> p (BoundVar n))
instance JboShow JboVPred where
    -- XXX: not knowing its arity, we can't actually show a vpred...
    -- so we just show the unary pred instead.
    logjboshow jbo vp = logjboshow jbo $ vPredToPred vp

logjboshowpred jbo@False p =
    withShuntedRelVar $ \n -> logjboshow jbo $ p n
logjboshowpred jbo@True p = withNext SVar $ \v ->
     case p v of
	 Rel sb ts | isJust $ elemIndex (BoundVar v) ts -> do
	     s <- logjboshow jbo sb
	     let i = 1 + fromJust (elemIndex (BoundVar v) ts)
		 ts' = tail $ case i of
			 1 -> ts
			 _ -> swapFinite ts 0 (i-1)
		 s' = case i of
			 1 -> s
			 _ -> seToStr i ++ " " ++ s
	     case ts' of
		 [] -> return s'
		 _ -> do
		     tss <- mapM jboshow ts'
		     let ptss = positionallyTaggedTerms ts' tss
		     return $ s' ++ if null ptss then ""
			else " be " ++ intercalate " bei " ptss
	 _ -> withShuntedRelVar $ \n -> do
		 s <- logjboshow jbo (p n)
		 return $ "poi'i " ++ s ++ " kei"

instance JboShow JboRel where
    {-
    logjboshow jbo (ConnectedRels conn r r') = do
	s <- logjboshow jbo r
	s' <- logjboshow jbo conn
	s'' <- logjboshow jbo r'
	return $ if jbo
	    then s ++ " " ++ s' ++ " " ++ s''
	    else "(" ++ s ++ " " ++ s' ++ " " ++ s'' ++ ")"
    logjboshow jbo (PermutedRel n r) =
	((seToStr n ++ " ") ++) <$> logjboshow jbo r
    -}
    logjboshow jbo (TanruConnective con p p') = do
	[ps,ps'] <- mapM (logjboshow jbo) [p,p']
	cs <- logjboshowConn jbo "j" con
	if jbo
	    then return $ "ke " ++ ps ++ " ke'e " ++ cs ++ " ke " ++ ps' ++ " ke'e"
	    else return $ "<" ++ ps ++ ">" ++ cs ++ "<" ++ ps' ++ ">"
    logjboshow jbo (Tanru p r) =
      do rstr <- logjboshow jbo r
	 pstr <- logjboshow jbo p
	 if jbo
	    then return $ "ke " ++ pstr ++ " " ++ rstr ++ " ke'e"
	    else return $ "<" ++ pstr ++ "><" ++ rstr ++ ">"
    logjboshow jbo (ScalarNegatedRel n r) = do
	rs <- logjboshow jbo r
	return $ if jbo then n ++ " " ++ rs else "{"++n++"}("++rs++")"
    logjboshow jbo (Moi (Value q) m) | mexIsNumberOrLS q = do
	s <- logjboshownumber jbo q
	return $ s ++ " " ++ m
    logjboshow jbo (Moi t m) = do
	ts <- logjboshow jbo t
	return $ if jbo then "me " ++ ts ++ " me'u " ++ m
	    else bracket '[' ts ++ " " ++ m
    logjboshow jbo (AbsPred a (JboNPred arity p)) =
	do withShuntedLambdas arity (\ns -> do
	    ps <- logjboshow jbo (p (map BoundVar ns))
	    as <- logjboshow jbo a
	    return $ if jbo then as ++ " " ++ ps ++ " kei" 
		else as ++ "[" ++ ps ++ "]" )
    logjboshow jbo (AbsProp a p) = do
	ps <- logjboshow jbo p
	as <- logjboshow jbo a
	return $ if jbo then as ++ " " ++ ps ++ " kei" 
		else as ++ "[" ++ ps ++ "]"
    logjboshow jbo (Among t) = do
	s <- logjboshow jbo t
	return $ if jbo then "me " ++ s ++ " me'u" else bracket '(' s ++ " >= "
    logjboshow jbo Equal =
	return $ if jbo then "du" else "="
    logjboshow jbo (UnboundBribasti (TUGOhA g n)) = return $
	(if jbo then unwords else concat) $
	    g : if n==1 then [] else ["xi",jbonum n]
    logjboshow jbo (BoundRVar n) = binding n >>= logjboshow jbo
    logjboshow True (RVar _) = return $ "NALSELTRO zei bu'a"
    logjboshow False (RVar _) = return $ "[UNBOUND RVar]"
    logjboshow jbo (UnboundBribasti (TUBrivla s)) = return s
    logjboshow jbo (OperatorRel op) =
	(if jbo then jbobracket "nu'a" "te'u" else bracket '[') <$> logjboshow jbo op
    logjboshow jbo (TagRel tag) = do
	tags <- logjboshow jbo tag
	return $ if jbo then "xo'i " ++ tags else "{" ++ tags ++ "}"
    logjboshow _ (Brivla s) = return s

instance JboShow SumtiAtom where
    logjboshow jbo (LerfuString s) = logjboshow jbo s
    logjboshow jbo v =
	if jbo then return $ case v of
	    Assignable n | n <= 5 -> "ko'" ++ vowelnum n
	    Assignable n | n <= 10 -> "fo'" ++ vowelnum (n-5)
	    Assignable n -> "ko'a xi " ++ jbonum n
	    Ri 1 -> "ri"
	    Ri n -> "ri xi " ++ jbonum n
	    Ra r -> r
	    MainBridiSumbasti n | n <= 5 -> "vo'" ++ vowelnum n
	    MainBridiSumbasti n -> "vo'a xi " ++ jbonum n
	else case v of
	    v -> do
		s <- logjboshow True v
		return $ "{" ++ s ++ "}"
instance JboShow ShowBindable where
    jboshow v = return $ case v of
	SVar n | n <= 3 -> "d" ++ vowelnum n
	SVar n -> "da xi " ++ jbonum n
	SRel 1 -> "ke'a"
	SRel n -> "ke'a xi " ++ jbonum n
	SLambda 1 1 -> "ce'u"
	SLambda l 1 -> "ce'u xi " ++ jbonum l
	SLambda l n ->
	    "ce'u xi " ++ jbonum l ++ " xi " ++ jbonum n
	SAss n | n <= 5 -> "ko'" ++ vowelnum n
	SAss n | n <= 10 -> "fo'" ++ vowelnum (n-5)
	SAss n -> "ko'a xi " ++ jbonum n
	SRVar n -> if n <= 3 then "bu'" ++ vowelnum n
	    else "bu'a xi " ++ jbonum n
	SRAss n | n <= 5 -> "brod" ++ vowelnum n
	SRAss n -> "broda xi " ++ jbonum n
    logshow v = case v of
	SVar n -> return $ "x" ++ show n
	SRel 1 -> return $ "_"
	SRel n -> return $ "_" ++ show n
	SLambda 1 n -> return $ "\\" ++ show n
	SLambda l n ->
	    return $ "\\" ++ bracket '(' (show l ++ "," ++ show n)
	SRVar n -> return $ "R" ++ show n
	_ -> bracket '{' <$> jboshow v
instance JboShow JboTerm where
    logjboshow False (Unfilled) = return " "
    logjboshow True (Unfilled) = return "BUG"
    logjboshow jbo (BoundVar n) = binding n >>= logjboshow jbo
    logjboshow jbo (Var n) = return $ if jbo then "lo NALSELTRO zei da ku" else "[UNBOUND Var]"
    logjboshow True (Constant n []) = return $ "cy " ++ jbonum n
    logjboshow False (Constant n []) = return $ "c" ++ show n
    logjboshow jbo (Constant n ts) = do
	ss <- mapM (logjboshow jbo) ts
	return $ if jbo
	    then "li ma'o fy" ++ jbonum n ++ " " ++
		(intercalate " " $ map ("mo'e "++) ss) ++ " lo'o"
	    else "f" ++ show n ++ "(" ++
		(intercalate "," ss) ++ ")"
    logjboshow True (Named s) = return $ "la " ++ s ++ "."
    logjboshow False (Named s) = return $ bracket '"' s
    logjboshow jbo (PredNamed p) = (if jbo then jbobracket "la poi'i" "ku'o ku"
	else brackets "[Name: ") <$> logjboshow jbo p
    logjboshow jbo (JboQuote (ParsedQuote ps)) =
	(if jbo then jbobracket "lu" "li'u" else brackets "<< ") <$> logjboshow jbo ps
    logjboshow jbo (JboErrorQuote vs) = return $
	(if jbo then jbobracket "lo'u" "le'u" else brackets "<{< ") $ unwords vs
    logjboshow jbo (JboNonJboQuote s) = return $
	let zoik = head
		[ zoik
		| n <- [0..]
		, let zoik = "zoi" ++ if n > 0 then ("k"++) $ concat $ replicate (n-1) "yk" else ""
		, not $ isInfixOf zoik s ]
	in (if jbo then "zoi " ++ zoik ++ " " else "<[< ") ++
	    s ++
	    (if jbo then " " ++ zoik else " >]>")
    logjboshow True (Valsi s) = return $ "zo " ++ s
    logjboshow False (Valsi s) = return $ "{" ++ s ++ "}"
    logjboshow jbo (UnboundSumbasti sa) = logjboshow jbo sa
    logjboshow _ (NonAnaph s) = return s
    logjboshow jbo (JoikedTerms joik t1 t2) = do
	[ts1,ts2] <- mapM (logjboshow jbo) [t1,t2]
	joiks <- logjboshow jbo joik
	return $ if jbo then ts1 ++ " " ++ joiks ++ " ke " ++ ts2 ++ " ke'e"
	    else "(" ++ ts1 ++ " {" ++ joiks ++ "} " ++ ts2 ++ ")"
    logjboshow jbo (QualifiedTerm qual t) = do
	ts <- logjboshow jbo t
	let quals = case qual of {LAhE l -> l; NAhE_BO n -> n ++ " bo"}
	return $ if jbo
	    then quals ++ " " ++ ts ++ " lu'u"
	    else "{" ++ quals ++ "}(" ++ ts ++ ")"
    logjboshow True (Value m) = ("li "++) . (++" lo'o") <$> logjboshow True m
    logjboshow False (Value m) = logjboshow False m
    logjboshow True (TheMex m) = ("me'o "++) . (++" lo'o") <$> logjboshow True m
    logjboshow False (TheMex m) = bracket '[' . ("MEX: "++) <$> logjboshow False m
	

vowelnum 1 = "a"
vowelnum 2 = "e"
vowelnum 3 = "i"
vowelnum 4 = "o"
vowelnum 5 = "u"
jbonum 0 = "no"
jbonum 1 = "pa"
jbonum 2 = "re"
jbonum 3 = "ci"
jbonum 4 = "vo"
jbonum 5 = "mu"
jbonum 6 = "xa"
jbonum 7 = "ze"
jbonum 8 = "bi"
jbonum 9 = "so"
jbonum n = jbonum (n `div` 10) ++ jbonum (n `mod` 10)

seToStr 2 = "se"
seToStr 3 = "te"
seToStr 4 = "ve"
seToStr 5 = "xe"
seToStr n = "se xi " ++ jbonum n

faToStr 1 = "fa"
faToStr 2 = "fe"
faToStr 3 = "fi"
faToStr 4 = "fo"
faToStr 5 = "fu"
faToStr n = "fa xi " ++ jbonum n

instance JboShow Int where
    logjboshow True n = return $ jbonum n
    logjboshow False n = return $ show n

instance JboShow JboProp
    where {logjboshow jbo p = (if jbo then unwords else concat)
				<$> logjboshow' jbo [] p
	where
	  logjboshow' :: Bool -> [String] -> JboProp -> Bindful ShowBindable [String]
	  {-
	  logjboshow' True ps (Quantified (Gadri gadri) r p) =
	      withNextAssignable $ \n ->
		  do vs <- logjboshow jbo (BoundVar n)
		     rss <- logjboshowpred jbo (fromJust r)
		     logjboshow' jbo (ps ++ [gadri] ++ [rss] ++
			 ["ku","goi",vs]) (p n)
	  -}
	  logjboshow' True ps (Quantified QuestionQuantifier r p) =
	      withNext SAss $ \n -> do
		as <- logjboshow jbo (BoundVar n)
		rss <- logjboshowRestriction jbo r
		logjboshow' jbo (ps ++ ["ma"] ++
		    rss ++ (if null rss then [] else ["zi'e"]) ++
		    ["goi",as]) (p n)
	  logjboshow' True ps (Quantified (RelQuantifier QuestionQuantifier) _ p) =
	      withNext SRAss $ \n ->
		  do as <- logjboshow jbo (BoundRVar n)
		     logjboshow' jbo (ps ++ ["mo","cei",as]) (p n)
	  logjboshow' jbo ps (Quantified (RelQuantifier q) _ p) =
	    withNext SRVar $ \n -> do
		qs <- logjboshow jbo q
		rvs <- logjboshow jbo (BoundRVar n)
		logjboshow' jbo (ps ++
		    [qs, if jbo then rvs else " " ++ rvs ++ ". "]) (p n)
	  logjboshow' jbo ps (Quantified q r p) =
	      withNext SVar $ \n ->
		  do qs <- logjboshow jbo q
		     vs <- logjboshow jbo (BoundVar n)
		     rss <- logjboshowRestriction jbo r
		     logjboshow' jbo (ps ++
			 [qs, (if jbo then "" else " ") ++ vs] ++ rss) (p n)
	  logjboshow' jbo ps (Modal (WithEventAs t) p) = do
	    ts <- logjboshow jbo t
	    logjboshow' jbo (ps ++ if jbo then ["fi'o","du"] ++ [ts] else [ts] ++ ["=. "]) p
	  logjboshow' jbo ps (Modal QTruthModal p) =
	    logjboshow' jbo (ps ++ if jbo then ["xu","kau"] else ["?. "]) p
	  logjboshow' jbo ps (Modal (JboTagged tag mt) p) = do
	    tags <- logjboshow jbo tag
	    mtl <- maybeToList <$> traverse (logjboshow jbo) mt
	    logjboshow' jbo (ps ++ if jbo
		then [tags] ++ take 1 (mtl ++ ["ku"])
		else ["(",tags,")","("] ++ mtl ++ ["). "]) p
	  logjboshow' jbo ps (Modal NonVeridical p) =
	    (if jbo then ("ju'a nai":) else ("non-veridical: ":)) <$>
		logjboshow' jbo ps p
	  logjboshow' jbo ps p | ps /= [] =
	      do ss <- logjboshow' jbo [] p
	         return $ ps ++ [if jbo then "zo'u" else ""] ++ ss
	  logjboshow' jbo [] (Connected c p1 p2) =
	      do ss1 <- logjboshow' jbo [] p1
	         ss2 <- logjboshow' jbo [] p2
	         return $ if jbo then case c of And -> ["ge"]
					        Or -> ["ga"]
					        Impl -> ["ga", "nai"]
					        Equiv -> ["go"]
	      			++ ss1 ++ ["gi"] ++ ss2
	      		   else ["("] ++ ss1 ++
	      		        [" "++show c++" "] ++ ss2 ++ [")"]
	  logjboshow' jbo [] (NonLogConnected joik p1 p2) =
	      do ss1 <- logjboshow' jbo [] p1
	         ss2 <- logjboshow' jbo [] p2
		 joiks <- logjboshow jbo joik
	         return $ if jbo then [joik,"gi"]
	      			++ ss1 ++ ["gi"] ++ ss2
	      		   else ["("] ++ ss1 ++
	      		        [" {"++joik++"} "] ++ ss2 ++ [")"]
	  logjboshow' jbo [] (Not p) =
	      do ss <- logjboshow' jbo [] p
	         return $ (if jbo then ["na","ku"] else ["!"]) ++ ss
	  logjboshow' jbo@True [] (Rel r []) =
	      do s <- jboshow r
	         return [s]
	  logjboshow' True [] (Rel r (x1:xs)) =
	      do fore <- if x1 == Unfilled then return []
		    else (\x->[x]) <$> jboshow x1
	         rs <- jboshow r
	         ss <- mapM jboshow xs
	         return $ fore ++ [rs] ++ positionallyTaggedTerms xs ss
	  logjboshow' False [] (Rel r ts) =
	      do s <- logshow r
		 tss <- mapM logshow ts
	         return $
	             [s ++ "(" ++ (intercalate "," tss) ++ ")"]
	  logjboshow' True [] Eet = return ["jitfa to SPOFU toi"]
	  logjboshow' False [] Eet = return ["_|_ (BUG)"]

	  logjboshowRestriction jbo Nothing = return $ if jbo then [] else [". "]
	  logjboshowRestriction jbo (Just r) = do
	    ss <- withShuntedRelVar (\m -> logjboshow' jbo [] (r m) )
	    return $ [if jbo then "poi" else ":("]
		++ ss
		++ [if jbo then "ku'o" else "). "]
	  }

positionallyTaggedTerms :: [JboTerm] -> [String] -> [String]
positionallyTaggedTerms xs ss = [
    (if skipped then faToStr n ++ " " else "") ++ s
    | (s,x,lastx,n) <- zip4 ss xs (Nothing:map Just xs) [2..]
    , x /= Unfilled
    , let skipped = lastx == Just Unfilled
    ]

instance JboShow Texticule where
    logjboshow jbo (TexticuleFrag f) = logjboshow jbo f
    logjboshow jbo (TexticuleProp p) = logjboshow jbo p
instance JboShow JboFragment where
    logjboshow jbo (JboFragTerms ts) =
	(if not jbo then bracket '[' . ("Fragment: "++) else id) <$>
	    logjboshowlist jbo ts
    logjboshow jbo _ = return $ if jbo then "li'o" else "[Fragment]"

instance JboShow JboText where
    jboshow fps = intercalate "\n.i " <$> mapM jboshow fps
    logshow fps = intercalate "\n" <$> mapM logshow fps
