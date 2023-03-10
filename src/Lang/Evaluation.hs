module Lang.Evaluation where

import Lang.Lang
import Lang.Operation
import Lang.Denotation
import Lang.Parser

import Logic.Proof

{-# INLINE std #-}
std :: GlobalEnv
std = loadFile "progs/std.xr"


evalExample :: String -> Val
evalExample s = eval std [] (parseString s)

traceExample :: String -> Proof EvalJ
traceExample s = trace std (parseString s)

