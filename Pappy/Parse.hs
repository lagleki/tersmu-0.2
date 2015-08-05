module Pappy.Parse(module Pappy.Parse, module Pappy.Basic, module Pappy.Pos) where

-- This contains the parsing monad and is only needed with the --monad option.
-- It allows mixing handwritten and pappy generated parsers.

import Data.Char

import Pappy.Pos
import Pappy.Basic

-- BEGIN CODE

newtype Parser d v = Parser { unParser :: d -> Result d v }

class Derivs d where
	dvPos	:: d -> Pos
	dvChar	:: d -> Result d Char

---------- Basic parsing combinators

infixl 2 </>		-- ordered choice
infixl 1 <?>		-- error labeling
infixl 1 <?!>		-- unconditional error labeling

-- Standard monadic combinators
instance Derivs d => Monad (Parser d) where

	-- Sequencing combinator
	(Parser p1) >>= f = Parser parse

		where parse dvs = first (p1 dvs)

		      first (Parsed val rem err) =
			let Parser p2 = f val
			in second err (p2 rem)
		      first (NoParse err) = NoParse err

		      second err1 (Parsed val rem err) =
			Parsed val rem (joinErrors err1 err)
		      second err1 (NoParse err) =
			NoParse (joinErrors err1 err)

	-- Result-producing combinator
	return x = Parser (\dvs -> Parsed x dvs (nullError dvs))

	-- Failure combinator
	fail [] = Parser (\dvs -> NoParse (nullError dvs))
	fail msg = Parser (\dvs -> NoParse (msgError (dvPos dvs) msg))

instance Derivs d => Functor (Parser d) where
    fmap f action = do r <- action; return (f r)

-- Ordered choice
(</>) :: Derivs d => Parser d v -> Parser d v -> Parser d v
(Parser p1) </> (Parser p2) = Parser parse

		where parse dvs = first dvs (p1 dvs)

		      first dvs (result @ (Parsed val rem err)) = result
		      first dvs (NoParse err) = second err (p2 dvs)

		      second err1 (Parsed val rem err) =
			Parsed val rem (joinErrors err1 err)
		      second err1 (NoParse err) =
			NoParse (joinErrors err1 err)

-- Semantic predicate: 'satisfy <parser> <pred>' acts like <parser>
-- but only succeeds if the result it generates satisfies <pred>.
satisfy :: Derivs d => Parser d v -> (v -> Bool) -> Parser d v
satisfy (Parser p) test = Parser parse

		where parse dvs = check dvs (p dvs)

		      check dvs (result @ (Parsed val rem err)) =
			if test val then result
				    else NoParse (nullError dvs)
		      check dvs none = none

-- Syntactic predicate: 'followedBy <parser>' acts like <parser>
-- but does not consume any input.
followedBy :: Derivs d => Parser d v -> Parser d v
followedBy (Parser p) = Parser parse

	where parse dvs = case (p dvs) of
		Parsed val rem err -> Parsed val dvs (nullError dvs)
		err -> err

-- Negative syntactic predicate: 'followedBy <parser>' invokes <parser>,
-- then succeeds without consuming any input if <parser> fails,
-- and fails if <parser> succeeds.
notFollowedBy :: Derivs d => Parser d v -> Parser d ()
notFollowedBy (Parser p) = Parser parse

	where parse dvs = case (p dvs) of
		Parsed val rem err -> NoParse (nullError dvs)
		NoParse err -> Parsed () dvs (nullError dvs)

-- Optional combinator: 'optional <parser>' invokes <parser>,
-- then produces the result 'Just <v>' if <parser> produced <v>,
-- or else produces the success result 'Nothing'
-- without consuming any input if <parser> failed.
optional :: Derivs d => Parser d v -> Parser d (Maybe v)
optional p = (do v <- p; return (Just v)) </> return Nothing

---------- Iterative combinators
-- Note: use of these combinators can break
-- a packrat parser's linear-time guarantee.

-- Zero or more repetition combinator:
-- 'many <parser>' invokes <parser> repeatedly until it fails,
-- collecting all success result values into a list.
-- Always succeeds, producing an empty list in the degenerate case.
many :: Derivs d => Parser d v -> Parser d [v]
many p = (do { v <- p; vs <- many p; return (v : vs) } )
	 </> return []

-- One or more repetition combinator:
-- 'many1 <parser>' invokes <parser> repeatedly until it fails,
-- collecting all success result values into a list.
-- Fails if <parser> does not succeed even once.
many1 :: Derivs d => Parser d v -> Parser d [v]
many1 p = do { v <- p; vs <- many p; return (v : vs) }

-- One or more repetitions with a separator:
-- 'sepBy1 <parser> <separator>' scans one or more iterations of <parser>,
-- with a match of <separator> between each instance.
-- Only the results of <parser> are collected into the final result list.
sepBy1 :: Derivs d => Parser d v -> Parser d vsep -> Parser d [v]
sepBy1 p psep = do v <- p
		   vs <- many (do { psep; p })
		   return (v : vs)

-- Zero or more repetitions with a separator:
-- like sepBy1, but succeeds with an empty list if nothing can be parsed.
sepBy :: Derivs d => Parser d v -> Parser d vsep -> Parser d [v]
sepBy p psep = sepBy1 p psep </> return []

-- Zero or more repetitions with a terminator
endBy :: Derivs d => Parser d v -> Parser d vend -> Parser d [v]
endBy p pend = many (do { v <- p; pend; return v })

-- One or more repetitions with a terminator
endBy1 :: Derivs d => Parser d v -> Parser d vend -> Parser d [v]
endBy1 p pend = many1 (do { v <- p; pend; return v })

-- One or more repetitions with a separator or terminator:
-- 'sepEndBy1 <parser> <septerm>' scans for a sequence of <parser> matches
-- in which instances are separated by <septerm>,
-- and if a <septerm> is found following the last <parser> match
-- then it is consumed as well.
sepEndBy1 :: Derivs d => Parser d v -> Parser d vsep -> Parser d [v]
sepEndBy1 p psep = do v <- sepBy1 p psep; optional psep; return v

-- Zero or more repetitions with a separator or terminator.
sepEndBy :: Derivs d => Parser d v -> Parser d vsep -> Parser d [v]
sepEndBy p psep = do v <- sepBy p psep; optional psep; return v

-- One or more repetitions separated by left-associative operators.
-- 'chainl1 <term> <oper>' matches instances of <term> separated by <oper>,
-- but uses the result of <oper> as a left-associative binary combinator:
-- e.g., 't1 op t2 op t3' is interpreted as '(t1 op t2) op t3'
chainl1 :: Derivs d => Parser d v -> Parser d (v->v->v) -> Parser d v
chainl1 p psep =
	let psuffix z = (do f <- psep
			    v <- p
			    psuffix (f z v))
			</> return z
	in do v <- p
	      psuffix v

-- Zero or more repetitions separated by left-associative operators.
chainl :: Derivs d => Parser d v -> Parser d (v->v->v) -> v -> Parser d v
chainl p psep z = chainl1 p psep </> return z

-- One or more repetitions separated by left-associative operators:
-- e.g., 't1 op t2 op t3' is interpreted as 't1 op (t2 op t3)'
chainr1 :: Derivs d => Parser d v -> Parser d (v->v->v) -> Parser d v
chainr1 p psep = (do v <- p
		     f <- psep
		     w <- chainr1 p psep
		     return (f v w))
		 </> p

-- Zero or more repetitions separated by left-associative operators.
chainr :: Derivs d => Parser d v -> Parser d (v->v->v) -> v -> Parser d v
chainr p psep z = chainr1 p psep </> return z

-- N-ary ordered choice:
-- given a list of parsers producing results of the same type,
-- try them all in order and use the first successful result.
choice :: Derivs d => [Parser d v] -> Parser d v
choice [p] = p
choice (p:ps) = p </> choice ps

---------- Error handling
failAt :: Derivs d => Pos -> String -> Parser d v
failAt pos msg = Parser (\dvs -> NoParse (msgError pos msg))

-- Annotate a parser with a description of the construct to be parsed.
-- The resulting parser yields an "expected" error message
-- if the construct cannot be parsed
-- and if no error information is already available
-- indicating a position farther right in the source code
-- (which would normally be more localized/detailed information).
(<?>) :: Derivs d => Parser d v -> String -> Parser d v
(Parser p) <?> desc = Parser $ \dvs ->
    errorAnnotate False desc (dvPos dvs) (p dvs)

-- Stronger version of the <?> error annotation operator above,
-- which unconditionally overrides any existing error information.
(<?!>) :: Derivs d => Parser d v -> String -> Parser d v
(Parser p) <?!> desc = Parser $ \dvs ->
    errorAnnotate True desc (dvPos dvs) (p dvs)

nullError dvs = ParseError (dvPos dvs) []

eofError dvs = msgError (dvPos dvs) "end of input"

expected :: Derivs d => String -> Parser d v
expected desc = Parser (\dvs -> NoParse (expError (dvPos dvs) desc))

unexpected :: Derivs d => String -> Parser d v
unexpected str = fail ("unexpected " ++ str)

---------- Character-oriented parsers

-- 'anyChar' matches any single character.
anyChar :: Derivs d => Parser d Char
anyChar = Parser dvChar

-- 'char <c>' matches the specific character <c>.
char :: Derivs d => Char -> Parser d Char
char ch = satisfy anyChar (\c -> c == ch) <?> show ch

-- 'oneOf <s>' matches any character in string <s>.
oneOf :: Derivs d => [Char] -> Parser d Char
oneOf chs = satisfy anyChar (\c -> c `elem` chs)
	    <?> ("one of the characters " ++ show chs)

-- 'noneOf <s>' matches any character not in string <s>.
noneOf :: Derivs d => [Char] -> Parser d Char
noneOf chs = satisfy anyChar (\c -> not (c `elem` chs))
	     <?> ("any character not in " ++ show chs)

-- 'string <s>' matches all the characters in <s> in sequence.
string :: Derivs d => String -> Parser d String
string str = p str <?> show str

	where p [] = return str
	      p (ch:chs) = do { char ch; p chs }

-- 'stringFrom <ss>' matches any string in the list of strings <ss>.
-- If any strings in <ss> are prefixes of other strings in <ss>,
-- then the prefixes must appear later in the list
-- in order for the longer strings to be recognized at all.
stringFrom :: Derivs d => [String] -> Parser d String
stringFrom [str] = string str
stringFrom (str : strs) = string str </> stringFrom strs

-- Match an uppercase letter.
upper :: Derivs d => Parser d Char
upper = satisfy anyChar isUpper <?> "uppercase letter"

-- Match a lowercase letter.
lower :: Derivs d => Parser d Char
lower = satisfy anyChar isLower <?> "lowercase letter"

-- Match any letter.
letter :: Derivs d => Parser d Char
letter = satisfy anyChar isAlpha <?> "letter"

-- Match any letter or digit.
alphaNum :: Derivs d => Parser d Char
alphaNum = satisfy anyChar isAlphaNum <?> "letter or digit"

-- Match any digit.
digit :: Derivs d => Parser d Char
digit = satisfy anyChar isDigit <?> "digit"

-- Match any hexadecimal digit.
hexDigit :: Derivs d => Parser d Char
hexDigit = satisfy anyChar isHexDigit <?> "hexadecimal digit (0-9, a-f)"

-- Match any octal digit.
octDigit :: Derivs d => Parser d Char
octDigit = satisfy anyChar isOctDigit <?> "octal digit (0-7)"

-- Match a newline.
newline :: Derivs d => Parser d Char
newline = char '\n'

-- Match a tab character.
tab :: Derivs d => Parser d Char
tab = char '\t'

-- Match any whitespace character (space, tab, newline, etc.).
space :: Derivs d => Parser d Char
space = satisfy anyChar isSpace <?> "whitespace character"

-- Match a sequence of zero or more whitespace characters.
spaces :: Derivs d => Parser d [Char]
spaces = many space

-- Match the end of file (i.e., "the absence of a character").
eof :: Derivs d => Parser d ()
eof = notFollowedBy anyChar <?> "end of input"

---------- Parser state manipulation combinators

-- Combinator to get the Derivs object for the current position:
-- e.g., 'dvs <- getDerivs' as part of a 'do' sequence.
getDerivs :: Derivs d => Parser d d
getDerivs = Parser (\dvs -> Parsed dvs dvs (nullError dvs))

-- Combinator to set the Derivs object used for subsequent parsing;
-- typically used to change parsing state elements in the Derivs tuple.
setDerivs :: Derivs d => d -> Parser d ()
setDerivs newdvs = Parser (\dvs -> Parsed () newdvs (nullError dvs))

-- Get the current position in the input text.
getPos :: Derivs d => Parser d Pos
getPos = Parser (\dvs -> Parsed (dvPos dvs) dvs (nullError dvs))
