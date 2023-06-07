{-# LANGUAGE PatternSynonyms #-}

module Lang.Lang where

import Display.Latex

import Data.List ((\\), intercalate)



{-- Data Types --}

type Var = String

data Expr 
  = EInt Int
  | EBool Bool
  | EStr String
  | EChar Char
  | EVar Var
  | ELet Var Expr Expr
  | EOp Expr BinOp Expr
  | ELam Var Expr
  | EApp Expr Expr
  | EIf Expr Expr Expr
  | EList [Expr]
  deriving Eq

data BinOp = Add | Mul | Sub | Div | Eq | LEq | Lt | Or | And | Gt | GEq | NEq | Append  deriving Eq



data Val
  = VInt Int
  | VBool Bool
  | VStr String
  | VChar Char
  | VList [Val]
  | VClosure Var Expr LocalEnv ValueName

type ValueName = [Expr] -- This will end up being nonempty

pattern VClo :: Var -> Expr -> LocalEnv -> Val
pattern VClo v e l <- VClosure v e l _ where
  VClo v e l = VClosure v e l []

type LocalEnv = [(Var, Val)]
type GlobalEnv = [(Var, Expr)]



{-- Functions --}

freeVars :: Expr -> [Var]
freeVars e = case e of
  EVar v  -> [v]
  ELet v e1 e2 -> freeVars e1 ++ (freeVars e2 \\ [v])
  EOp e1 _ e2 -> freeVars e1 ++ freeVars e2
  ELam v e -> freeVars e \\ [v]
  EApp e1 e2 -> freeVars e1 ++ freeVars e2
  EIf e1 e2 e3 -> freeVars e1 ++ freeVars e2 ++ freeVars e3
  EList es -> concatMap freeVars es
  _ -> []


flattenApp :: Expr -> (Expr,[Expr])
flattenApp e = case e of
  EApp e1 e2 -> let (e',es) = flattenApp e1 in (e',es ++ [e2])
  _          -> (e,[])

unflattenApp :: Expr -> [Expr] -> Expr
unflattenApp e [] = e
unflattenApp e (e':es) = unflattenApp (EApp e e') es

-- treeMap :: (Expr -> Expr) -> Expr -> Expr
-- treeMap f e = case e of
--   ELet v e1 e2 -> f $ ELet v (treeMap f e1) (treeMap f e2)
--   EOp e1 o e2  -> f $ EOp (treeMap f e1) o (treeMap f e2)
--   ELam v e     -> f $ ELam v (treeMap f e)
--   EApp e1 e2   -> f $ EApp (treeMap f e1) (treeMap f e2)
--   EIf e1 e2 e3 -> f $ EIf (treeMap f e1) (treeMap f e2) (treeMap f e3)
--   EList es     -> f $ EList (map (treeMap f) es)
--   _            -> f e

-- Takes a function that takes a new expression, and returns a new expression
treeMap :: (Expr -> Expr) -> Expr -> Expr
treeMap f e = treeMap' (const f) e

-- Takes a function that accepts the original expression and returns a new expression, and returns a new expression
treeMap' :: (Expr -> Expr -> Expr) -> Expr -> Expr
treeMap' f e = case e of
  ELet v e1 e2 -> f e $ ELet v (treeMap' f e1) (treeMap' f e2)
  EOp e1 o e2  -> f e $ EOp (treeMap' f e1) o (treeMap' f e2)
  ELam v e     -> f e $ ELam v (treeMap' f e)
  EApp e1 e2   -> f e $ EApp (treeMap' f e1) (treeMap' f e2)
  EIf e1 e2 e3 -> f e $ EIf (treeMap' f e1) (treeMap' f e2) (treeMap' f e3)
  EList es     -> f e $ EList (map (treeMap' f) es)
  _            -> f e e


substExpr :: Expr -> Expr -> Expr -> Expr
substExpr a b e = treeMap subst e
  where subst a' | a == a' = b
                 | otherwise = a'

(~>) a b = substExpr a b

substVar :: Var -> Expr -> Expr -> Expr
substVar v e1 e2 = treeMap' subst e2
  where subst e (EVar v')     | v == v' = e1
        subst e (ELam v' _)   | v == v' = e
        subst e (ELet v' _ _) | v == v' = e
        subst e e' = e'

(/~>) v e = substVar v e

-- f :: [a -> a] -> a -> a
-- foldl (.) id

fillEnv :: LocalEnv -> Expr -> Expr
fillEnv env e = foldl (.) id substs e -- foldl (\ v e' -> (/~>) v e') e env'
  where substs = [v /~> (embed e') | v <- map fst env', let (Just e') = lookup v env']
        env' = filter (not . isClosure . snd) env
        isClosure (VClo _ _ _) = True
        isClosure _                = False

 

-- fillEnv env 




containsApp :: Expr -> Bool
containsApp (EApp _ _) = True
containsApp (ELet _ e1 e2) = containsApp e1 || containsApp e2
containsApp (EOp e1 _ e2) = containsApp e1 || containsApp e2
containsApp (ELam _ e) = containsApp e
containsApp (EIf e1 e2 e3) = containsApp e1 || containsApp e2 || containsApp e3
containsApp (EList es) = any containsApp es
containsApp _ = False




embed :: Val -> Expr
embed (VInt n)  = EInt n
embed (VBool b) = EBool b
embed (VStr s)  = EStr s
embed (VChar c) = EChar c
embed (VList vs) = EList (map embed vs)
embed (VClo _ _ _) = error "cannot embed a closure"




{--   Instances   --}

instance Eq Val where
  (VClo x e env) == (VClo x' e' env') = x == x && e == e && env == env'
  a == b = (compare a b == EQ)

instance Ord Val where
  compare (VInt a) (VInt b)   = compare a b
  compare (VBool a) (VBool b) = compare a b
  compare (VStr a) (VStr b)   = compare a b
  compare (VList a) (VList b) = compare a b

  compare (VClo _ _ _) (VClo _ _ _)
                              = error "cannot compare closures"
  compare _ _                 = error "cannot compare values of different types"


instance Show Expr where
  show (EInt n)  = show n
  show (EBool b) = show b
  show (EStr s)  = show s
  show (EChar c) = show c
  show (EVar v)  = v
  show (ELet v e1 e2) = "let " ++ v ++ " = " ++ show e1 ++ " in " ++ show e2
  show (EOp e1 o e2) = "(" ++ show e1 ++ " " ++ show o ++ " " ++ show e2 ++ ")"
  show (EApp e1 e2) 
    = case e2 of
        (EInt _)  -> show e1 ++ " " ++ show e2
        (EBool _) -> show e1 ++ " " ++ show e2
        (EStr _)  -> show e1 ++ " " ++ show e2
        (EChar _) -> show e1 ++ " " ++ show e2
        (EVar _)  -> show e1 ++ " " ++ show e2
        _         -> show e1 ++ " (" ++ show e2 ++ ")"
  show (ELam v e) = "(fun " ++ v ++ " -> " ++ show e ++ ")"
  show (EList es) = "[" ++ intercalate ", " (map show es) ++ "]"
  show (EIf e1 e2 e3) = "if " ++ show e1 ++ " then " ++ show e2 ++ " else " ++ show e3

instance Show BinOp where
  show Add = "+"
  show Mul = "*"
  show Sub = "-"
  show Div = "/"
  show Eq  = "=="
  show LEq = "<="
  show Lt  = "<"
  show Gt  = ">"
  show Or  = "||"
  show And = "&&"
  show GEq = ">="
  show NEq = "/="
  show Append = "++"

instance Show Val where
  show (VInt n)  = show n
  show (VBool b) = show b
  show (VStr s)  = show s
  show (VChar c) = show c
  show (VList vs) = "[" ++ intercalate ", " (map show vs) ++ "]"
  -- show (VClosure x e _ ns) = show (head ns)
  show (VClosure x e _ [n]) = show n
  show (VClosure x e _ (_:n:_)) = show n
  -- show (VClosure x e _ (n:_)) = show n
  -- show (VClosure x e _ ns) = "(closure " ++ x ++ " -> " ++ show e ++ "," ++ show ns ++ ")"


instance Latex Expr where
  latex (EInt n)  = show n
  latex (EBool b) = show b
  latex (EStr s)  = show s
  latex (EChar c) = show c
  latex (EVar v)  = v
  latex (ELet v e1 e2) = "let " ++ v ++ " = " ++ latex e1 ++ " in " ++ latex e2
  latex (EOp e1 o e2) = "(" ++ latex e1 ++ " " ++ latex o ++ " " ++ latex e2 ++ ")"
  latex (EApp e1 e2) 
    = case e2 of
        (EInt _)  -> latex e1 ++ " " ++ latex e2
        (EBool _) -> latex e1 ++ " " ++ latex e2
        (EStr _)  -> latex e1 ++ " " ++ latex e2
        (EChar _) -> latex e1 ++ " " ++ latex e2
        (EVar _)  -> latex e1 ++ " " ++ latex e2
        _         -> latex e1 ++ " (" ++ latex e2 ++ ")"
  latex (ELam v e) = "(fun " ++ v ++ " -> " ++ latex e ++ ")"
  latex (EList es) = "[" ++ intercalate ", " (map latex es) ++ "]"
  latex (EIf e1 e2 e3) = "if " ++ latex e1 ++ " then " ++ latex e2 ++ " else " ++ latex e3

instance Latex BinOp where
  latex = show

instance Latex Val where
  latex (VInt n)  = show n
  latex (VBool b) = show b
  latex (VStr s)  = show s
  latex (VChar c) = show c
  latex (VList vs) = "[" ++ intercalate ", " (map latex vs) ++ "]"
  latex (VClo x e _) = "(closure " ++ x ++ " -> " ++ latex e ++ ")"
