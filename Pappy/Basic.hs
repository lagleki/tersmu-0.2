module Pappy.Basic where

-- This module contains basic definitions needed for a pure pappy generated
-- parser

import Pappy.Pos

-- BEGIN CODE

---------- Data types used for parsing

data ErrorDescriptor =
	  Expected String
   	| Message String
        deriving(Eq)

data ParseError = ParseError {
			errorPos	:: Pos,
			errorDescrs	:: [ErrorDescriptor]
		}

data Result d v =
	  Parsed v d ParseError
        | NoParse ParseError

-- Join two ParseErrors, giving preference to the one farthest right,
-- or merging their descriptor sets if they are at the same position.
joinErrors :: ParseError -> ParseError -> ParseError
joinErrors (e @ (ParseError p m)) (e' @ (ParseError p' m')) =
	if p' > p || null m then e'
	else if p > p' || null m' then e
	else ParseError p (m `union` m') where
                union xs (y:ys) = f (reverse xs) ys where
                    f xs (y:ys) = if y `elem` xs then f xs ys else f (y:xs) ys
                    f xs [] = reverse xs

msgError pos msg = ParseError pos [Message msg]

-- Comparison operators for ParseError just compare relative positions.
instance Eq ParseError where
	ParseError p1 m1 == ParseError p2 m2	= p1 == p2
	ParseError p1 m1 /= ParseError p2 m2	= p1 /= p2

instance Ord ParseError where
	ParseError p1 m1 < ParseError p2 m2	= p1 < p2
	ParseError p1 m1 > ParseError p2 m2	= p1 > p2
	ParseError p1 m1 <= ParseError p2 m2	= p1 <= p2
	ParseError p1 m1 >= ParseError p2 m2	= p1 >= p2

	-- Special behavior: "max" joins two errors
	max p1 p2 = joinErrors p1 p2
	min p1 p2 = undefined

-- Show function for error messages
instance Show ParseError where
	show (ParseError pos []) =
		show pos ++ ": parse error"
	show (ParseError pos msgs) = expectmsg expects ++ messages msgs
	   where
		expects = getExpects msgs
		getExpects [] = []
		getExpects (Expected exp : rest) = exp : getExpects rest
		getExpects (Message msg : rest) = getExpects rest

		expectmsg [] = ""
		expectmsg [exp] = show pos ++ ": expecting " ++ exp ++ "\n"
		expectmsg [e1, e2] = show pos ++ ": expecting either "
					++ e1 ++ " or " ++ e2 ++ "\n"
		expectmsg (first : rest) = show pos ++ ": expecting one of: "
						++ first ++ expectlist rest
						++ "\n"
		expectlist [last] = ", or " ++ last
		expectlist (mid : rest) = ", " ++ mid ++ expectlist rest

		messages [] = []
		messages (Expected exp : rest) = messages rest
		messages (Message msg : rest) =
			show pos ++ ": " ++ msg ++ "\n" ++ messages rest

errorAnnotate :: Bool -> String -> Pos -> Result d v -> Result d v
errorAnnotate isStrict desc pos = munge where
    munge (Parsed v rem err) = Parsed v rem (fix err)
    munge (NoParse err) = NoParse (fix err)
    fix (err @ (ParseError p ms)) =
        if p > pos && not isStrict
            then err else expError pos desc

expError pos desc = ParseError pos [Expected desc]
