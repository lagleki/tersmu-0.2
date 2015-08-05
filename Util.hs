-- This file is part of tersmu
-- Copyright (C) 2014 Martin Bays <mbays@sdf.org>
--
-- This program is free software: you can redistribute it and/or modify
-- it under the terms of version 3 of the GNU General Public License as
-- published by the Free Software Foundation.
--
-- You should have received a copy of the GNU General Public License
-- along with this program.  If not, see http://www.gnu.org/licenses/.

module Util where

swap :: [a] -> Int -> Int -> [a]
swap as n m = [ if i == n then as!!m else
		if i == m then as!!n else as!!i | i <- [0..] ]

swapFinite as n m = take (length as) $ swap as n m

swapFiniteWithDefault :: a -> [a] -> Int -> Int -> [a]
swapFiniteWithDefault def ts n m = take (max (max n m + 1) (length ts)) $
	swap (ts ++ repeat def) n m
