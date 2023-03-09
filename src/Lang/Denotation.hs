module Lang.Denotation where

import Lang.Lang

import Data.Maybe (fromJust)



eval :: GlobalEnv -> LocalEnv -> Expr -> Val
eval d rho e = case e of
  EInt n  -> VInt n
  EBool b -> VBool b
  EStr s  -> VStr s
  EChar c -> VChar c
  EVar v | Just val <- lookup v rho -> val
         | Just e'  <- lookup v d -> eval d [] e'
         | otherwise -> error $ "unbound variable: " ++ v
  ELet v e1 e2 -> eval d ((v, eval d rho e1):rho) e2
  EOp e1 o e2  -> runBinOp o (eval d rho e1) (eval d rho e2)
  ELam v e     -> VClosure v e rho -- TODO: trim the closure environment?
  EApp _ _ | isBuildInApp e -> runBuildInApp d rho e
  EApp e1 e2   -> case (eval d rho e1, eval d rho e2) of
                    (VClosure v e env, x) -> eval d ((v, x):env) e
                    (_, _) -> error "cannot apply a non-closure value"
  EIf e1 e2 e3 -> case eval d rho e1 of
                    VBool b -> eval d rho (if b then e2 else e3)
                    _ -> error "condition must be a boolean"
  EList es     -> VList (map (eval d rho) es)



runBinOp :: BinOp -> Val -> Val -> Val
runBinOp op = case op of
  Add -> arith (+)
  Mul -> arith (*)
  Sub -> arith (-)
  Div -> arith div
  Eq  -> comp (==)
  LEq -> comp (<=)
  Lt  -> comp (<)
  Or  -> bool (||)
  And -> bool (&&)
  GEq -> comp (>=)
  NEq -> comp (/=)
  Append -> append
  where
    arith f (VInt a) (VInt b) = VInt (f a b)
    arith _ a b = error $ "binary operator expected integer arguments. " ++ show a ++ " " ++ show op ++ " " ++ show b
    comp f v1 v2 = VBool (f v1 v2)
    bool f (VBool a) (VBool b) = VBool (f a b)
    append (VList a) (VList b) = VList (a ++ b)
    append a b = error $ "only lists can be appended. " ++ show a ++ " ++ " ++ show b 


type BuiltInFun = [Val] -> Val
type Arity = Int

builtInDefs :: [(Var,(Arity,BuiltInFun))]
builtInDefs
  = [ ("print", (1, printFun))
    , ("head", (1, headFun))
    , ("tail", (1, tailFun))
    ]
  where printFun = undefined
        headFun [VList (x:_)] = x
        headFun [VList []]    = error "(builtin)head: empty list"
        headFun _             = error "(builtin)head: expected a list"
        tailFun [VList (_:xs)] = VList xs
        tailFun [VList []]     = VList []
        tailFun _              = error "(builtin)tail: expected a list"

isBuiltIn :: Var -> Bool
isBuiltIn v = v `elem` map fst builtInDefs

arity :: Var -> Arity
arity v = case lookup v builtInDefs of
            Just (a,_) -> a
            Nothing    -> error "arity: not a built-in function"

runBuiltIn :: Var -> [Val] -> Val
runBuiltIn f args | arity f == length args = f' args
  where f' = snd $ fromJust $ lookup f builtInDefs
runBuiltIn f _ = error $ "runBuiltIn: wrong number of arguments for " ++ f

isBuildInApp :: Expr -> Bool
isBuildInApp e = case flattenApp e of
                   (EVar f, args) -> isBuiltIn f && length args == arity f
                   _              -> False

runBuildInApp :: GlobalEnv -> LocalEnv -> Expr -> Val
runBuildInApp d rho e = case flattenApp e of
                          (EVar f, args) -> runBuiltIn f (map (eval d rho) args)
                          _              -> error "runBuildInApp: not a built-in application"

{--
-- fact = fun x -> if x == 0 then 1 else x * fact (x - 1)
globalTest :: GlobalEnv
globalTest = [("fact", ELam "x" (EIf (EOp (EVar "x") Eq (EInt 0)) (EInt 1) (EOp (EVar "x") Mul (EApp (EVar "fact") (EOp (EVar "x") Sub (EInt 1))))))]

-- fact 5
testExpr :: Expr
testExpr = EApp (EVar "fact") (EInt 5)
--}


-- id = fun x -> x
-- flip = fun f -> fun x -> fun y -> f y x
-- sub = fun x -> fun y -> x - y
globalTest :: GlobalEnv
globalTest = [("id", ELam "x" (EVar "x")), ("flip", ELam "f" (ELam "x" (ELam "y" (EApp (EApp (EVar "f") (EVar "y")) (EVar "x"))))), ("sub", ELam "x" (ELam "y" (EOp (EVar "x") Sub (EVar "y"))))]

-- flip sub 5 3
testExpr :: Expr
testExpr = EApp (EApp (EApp (EVar "flip") (EVar "sub")) (EInt 5)) (EInt 3)


