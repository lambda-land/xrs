module Lang.Evaluation where

import Lang.Lang
import Lang.Operation
import Lang.Denotation
import Lang.Parser

import Logic.Proof


{-# INLINE std #-}
std :: GlobalEnv
std = loadFile "progs/std.xr"

parseExample :: String -> Expr
parseExample = parseString

evalExample :: String -> Val
evalExample s = eval std [] (parseString s)

traceExample :: String -> Proof EvalJ
traceExample s = trace std (parseString s)

traceExpr :: Expr -> Proof EvalJ
traceExpr = trace std