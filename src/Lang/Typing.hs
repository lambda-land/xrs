{-# LANGUAGE ViewPatterns #-}

module Lang.Typing where

import Lang.Lang


type TypeVar = String

data Type
  = TInt
  | TBool
  | TStr
  | TChar
  | TList Type
  | TFun Type Type
  | TVar TypeVar
  | TError
  | TUnknown Int
  deriving Eq

type TypeKB = [(Expr,Type)]

type TypeEnv = [(Var,Type)]


{--
      x free in G     n fresh
  -----------------------------TypeVar
    G |- x -| G[x :: Unk(n)]


    t = typeof(v)
  ------------------------TypeVal
    G |- v -| G[v :: t]


    G |- e1 :: Int -| H     G |- e2 :: Int -| K     F = H union K
  -----------------------------------------------------------------
    G |- e1 + e2 -| G[e1 + e2 :: Int]





  ------------------------------
    G |- v -| G[v :: typeof(v)]

    x not in dom(G)     n fresh
  ------------------------------
    G |- x -| G[x :: Unk(n)]

  ------------------------------------------
    G |- e1 + e2 -| G[e1 :: Int, e2 :: Int, e1 + e2 :: Int]

  ------------------------------------------
    G |- e1 == e2 -| G[e1 :: t, e2 :: t, e1 == e2 :: Bool]


--}

addConstraint :: TypeKB -> Expr -> Type -> TypeKB
addConstraint kb e t = (e,t):kb

addConstraints :: TypeKB -> [(Expr,Type)] -> TypeKB
addConstraints kb [] = kb
addConstraints kb (c:cs)= addConstraints (addConstraint kb (fst c) (snd c)) cs

baseType :: Expr -> (Expr,Type)
baseType (EInt n) = (EInt n,TInt)
baseType (EBool b) = (EBool b,TBool)
baseType (EStr s) = (EStr s,TStr)
baseType (EChar c) = (EChar c,TChar)


-- constraints :: TypeKB -> Expr ->\ TypeKB
-- constraints kb (baseType -> (e,t)) = addConstraint kb e t
-- constraints kb e@(EOp e1 op e2) | op `elem` [Add,Mul,Sub,Div] = addConstraint (constraints kb e1 ++ constraints kb e2) e TInt
                                -- | otherwise = constraints kb e1 ++ constraints kb e2


-- disputeTypes 

constraints :: TypeKB -> Expr -> (TypeKB,Type)
constraints kb e = case e of
  EInt n -> (addConstraint kb (EInt n) TInt,TInt)
  EBool b -> (kb,TBool)
  EStr s -> (kb,TStr)
  EChar c -> (kb,TChar)
  EVar v -> (addConstraint kb (EVar v) (TUnknown (length kb)),(TUnknown (length kb)))
  ELet v e1 e2 -> let (kb1,t1) = constraints kb e1
                      (kb2,t2) = constraints (addConstraint kb1 (EVar v) t1) e2
                  in (kb2,t2)
  EOp e1 op e2 -> let (kb1,t1) = constraints kb e1
                      (kb2,t2) = constraints kb1 e2
                  in case op of
                    Add -> (addConstraints kb2 [(e,TInt),(e1,TInt),(e2,TInt)],TInt)
                    Sub -> (addConstraints kb2 [(e,TInt),(e1,TInt),(e2,TInt)],TInt)
                    Mul -> (addConstraints kb2 [(e,TInt),(e1,TInt),(e2,TInt)],TInt)
                    Div -> (addConstraints kb2 [(e,TInt),(e1,TInt),(e2,TInt)],TInt)
                    Eq -> (addConstraints kb2 [(e,TBool),(e1,t1),(e2,t2)],TBool)
  ELam v e -> let (kb1,t1) = constraints kb e
                  Just rt = lookup e kb1
                  Just t = lookup (EVar v) kb1
              in (addConstraint kb1 (ELam v e) (TFun t rt),TFun t rt)
  EApp e1 e2 -> let (kb1,t1) = constraints kb e1
                    (kb2,t2) = constraints kb1 e2
                in (addConstraint kb2 e t2,TFun t1 t2)
  EIf e1 e2 e3 -> let (kb1,t1) = constraints kb e1
                      (kb2,t2) = constraints kb1 e2
                      (kb3,t3) = constraints kb2 e3
                  in (addConstraint kb3 e t2,t2)
  EList es -> let (k ,ts) = foldr (\e (kb,ts) -> let (kb1,t1) = constraints kb e
                                                in (kb1,t1:ts)) (kb,[]) es
              in (k,TList (head ts))


instance Show Type where
  show TInt = "Int"
  show TBool = "Bool"
  show TStr = "String"
  show TChar = "Char"
  show (TList t) = "[" ++ show t ++ "]"
  show (TFun t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (TVar v) = v
  show TError = "Error"
  show (TUnknown n) = "Unk(" ++ show n ++ ")"