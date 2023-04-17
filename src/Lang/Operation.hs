module Lang.Operation where

import Lang.Lang
import Lang.Denotation

import Logic.Proof

import Display.Latex

import Data.List (intercalate)
import Data.Maybe (fromJust)


-- D, rho |- e => v
data EvalJ = EvalJ GlobalEnv LocalEnv Expr Val deriving Eq



-- NOTE: DO NOT RUN CHECKS DURING premises!! (unless you need to).
-- There should not be any validation until the axioms or when the system needs to be cashed out.

instance Explain EvalJ where
  
{--
  -------------------Lit
  D, rho |- v => v
--}
  premises (EvalJ d rho (EInt i) (VInt i'))   | i == i' = [[]]
  premises (EvalJ d rho (EBool b) (VBool b')) | b == b' = [[]]
  premises (EvalJ d rho (EStr s) (VStr s'))   | s == s' = [[]]
  premises (EvalJ d rho (EChar c) (VChar c')) | c == c' = [[]]

{--
  (x,v) in rho
  ------------------LocalVar
  D, rho |- x => v
--}
  premises (EvalJ d rho (EVar x) v) | (x,v) `elem` rho = [[]]

{--
  (x,e) in D     D, [] |- e => v
  -----------------------------------GlobalVar
  D, rho |- x => v
--}
  premises (EvalJ d rho (EVar f) v) | Just e <- lookup f d = [[EvalJ d [] e v]]

{--
  D, rho |- e1 => v1      D, rho |- e2 => v2       op(v1,v2) = v
  ------------------------------------------------------------------Op
  D, rho |- e1 op e2 => v
--}
  premises (EvalJ d rho (EOp e1 op e2) v) | runBinOp op v1 v2 == v 
    = [[EvalJ d rho e1 v1, EvalJ d rho e2 v2]]
    where v1 = eval d rho e1
          v2 = eval d rho e2

{--
  -----------------------------------------------Abs
  D, rho |- \x -> e => (closure x -> e, rho)
--}
  premises (EvalJ d rho (ELam x e) (VClo x' e' rho')) | x == x' && e == e' && rho == rho' = [[]]

{--
  D, rho |- ei => vi    f(e1,...,en)    arity(f) = n
  -------------------------------------------------------------------BuiltInApp
  D, rho |- f e1 ... en => v     (where f ranges over builtin vars)
--}
  premises (EvalJ d rho e@(EApp _ _) v) | isBuildInApp e, arity f == length es
    = [[EvalJ d rho ei vi | ei <- es, let vi = eval d rho ei]]
    where (EVar f, es) = flattenApp e

{--
  D, rho |- e1 => (closure x -> e',rho')     D, rho |- e2 => v2      D, rho'[x |-> v2] |- e' => v
  ---------------------------------------------------------------------------------------------------App
  D, rho |- e1 e2 => v
--}
  premises (EvalJ d rho (EApp e1 e2) v) | VClo x e' rho' <- eval d rho e1,
                                          v2 <- eval d rho e2
    = [[EvalJ d rho e1 (VClo x e' rho'), EvalJ d rho e2 v2, EvalJ d ((x,v2):rho') e' v]]

{--
  D, rho |- e1 => v'     D, rho[x |-> v'] |- e2 => v
  ------------------------------------------------------Let
  D, rho |- let x = e1 in e2 => v
--}
  premises (EvalJ d rho (ELet x e1 e2) v) = [[EvalJ d rho e1 v', EvalJ d ((x,v'):rho) e2 v]]
    where v' = eval d rho e1

{--
  D, rho |- e1 => True    D, rho |- e1 => v1
  -----------------------------------------------IfTrue
  D, rho |- if e1 then e2 else e3 => v1

  D, rho |- e1 => False    D, rho |- e2 => v2
  -----------------------------------------------IfFalse
  D, rho |- if e1 then e2 else e3 => v2
--}
  premises (EvalJ d rho (EIf e1 e2 e3) v)
    | VBool b <- eval d rho e1, b == True  = [[EvalJ d rho e1 (VBool True), EvalJ d rho e2 v]]
    | VBool b <- eval d rho e1, b == False = [[EvalJ d rho e1 (VBool False), EvalJ d rho e3 v]]


{--
  --------------------ListNil
  D, rho |- [] => []
--}
  premises (EvalJ d rho (EList []) (VList [])) = [[]]


{--
  D, rho |- ei => vi
  ------------------------------------------List
  D, rho |- [e1, ..., en] |- [v1, ..., vn]
--}
  premises (EvalJ d rho (EList es) (VList vs)) | length es == length vs
    = [[EvalJ d rho ei vi | (ei, vi) <- zip es vs]]


  premises _ = []



trace :: GlobalEnv -> Expr -> Proof EvalJ
trace d e = fromJust $ prove (EvalJ d [] e v)
-- trace d e = suppose (EvalJ d [] e v)
  where v = eval d [] e







instance Show EvalJ where
  show (EvalJ d rho e v) = show e ++ " => " ++ show v

  -- show (EvalJ d rho e v) = "{}" ++ "," ++ "[]" ++ " |- " ++ show e ++ " => " ++ show v
  -- show (EvalJ d rho e v) = "{}" ++ "," ++ showLocal rho ++ " |- " ++ show e ++ " => " ++ show v
    where showGlobal d = "{" ++ (intercalate ", " $ map fst d) ++ "}"
          showLocal rho = "[" ++ (intercalate ", " $ map (\(v, v') -> v ++ " -> " ++ show v') $ filter (\(v,_) -> v `elem` (freeVars e)) rho) ++ "]"

instance Latex EvalJ where
  latex (EvalJ d rho e v) = "\\{\\ \\}" ++ "," ++ localEnv ++ " \\vdash " ++ "\\code{" ++ latex e ++ "} "++ " \\Rightarrow " ++ "\\code{" ++ latex v ++ "}"
    where showGlobal d = "{" ++ (intercalate ", " $ map fst d) ++ "}"
          showLocal rho = "[" ++ (intercalate ", " $ map (\(v, v') -> "\\code{" ++ v ++ "} "++ " \\mapsto " ++ "\\code{" ++ latex v' ++ "}") $ filter (\(v,_) -> v `elem` (freeVars e)) rho) ++ "]"
          localEnv = showLocal rho -- "[\\ ]"