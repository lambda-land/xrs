-- File generated by the BNF Converter (bnfc 2.9.4.1).

-- Templates for pattern matching on abstract syntax
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

-- module Lang where
module Lang.ASTConverter where

-- import Prelude (($), Either(..), String, (++), Show, show)
import qualified Lang.AbsParser as AbsParser
import Data.List(intercalate)
import Lang.Lang

-- data Val = N Int | S String | C Char | B Bool | L [Val] | L' List | Abs OVar Expr Type | Err deriving (Eq,Show)

-- type TVar = String
-- type OVar = String 

-- data Type = TVar TVar | TBool | TInt | TArrow Type Type | TList Type | TTuple [Type] | TError deriving (Eq,Show)

-- data Pat = PVal Val | PList [Pat] | PWild deriving (Eq,Show)

-- data List = Cons Val List | Nil deriving (Eq,Show)



-- instance Show Val where
--   show (N n) = show n
--   show (B b) = show b
--   show (L vs) = show vs
--   show (Abs x e t) = "(\\" ++ x ++ " -> " ++ show e -- ++ " :: " ++ show t ++ ")"
--   show (L' l) = show l
--   show Err = "err"
--   show (S s) = s
--   show (C c) = show c


-- instance Show Pat where
--   show (PVal v) = show v
--   show (PList ps) = show ps
--   show PWild = "_"

-- instance Show List where
--   show = show . lToList

-- instance Show Expr where
--   show (Lit v) = show v
--   show (Var x) = x
--   show (Let x e1 e2) = "let " ++ x ++ " = " ++ show e1 ++ " in " ++ show e2 
--   show (LetRec x e1 e2) = "rec " ++ x ++ " = " ++ show e1 ++ " in " ++ show e2 
--   show (Op e1 op e2) = show e1 ++ " " ++ show op ++ " " ++ show e2 
--   show (App e1 (Lit v)) =  show e1 ++ " " ++  show v 
--   show (App e1 e2) =  show e1 ++ "(" ++ show e2 ++ ")"
--   show (Case e ps) = "(case " ++ show e ++ " of " ++ intercalate " | " (map show ps) ++ ")"
--   show (If e1 e2 e3) = "if " ++ show e1 ++ " then " ++ show e2 ++ " else " ++ show e3 ++ ""


-- instance Show BinOp where
--   show Add = "+"
--   show Mul = "*"
--   show Sub = "-"
--   show Div = "/"
--   show Eq = "=="
--   show LEq = "<=" 
--   show LE = "<"

-- lToList Nil = []
-- lToList (Cons v l) = v : lToList l

-- fromList [] = Nil
-- fromList (v:vs) = Cons v (fromList vs)

-- (.->) = TArrow

-- data Expr = Lit Val
--           | Var OVar
--           | Let OVar Expr Expr
--           | LetRec OVar Expr Expr
--           | Op Expr BinOp Expr
--           | App Expr Expr
--           | Case Expr [(Pat, Expr)]   
--           | If Expr Expr Expr 
--           deriving (Eq,Show)


-- data BinOp = Add | Mul | Sub | Div | Eq | LEq | LE | Or | And | GEq | NEq  deriving (Eq,Show)


type Err = Either String
type Result = Err String

failure :: Show a => a -> Result
failure x = Left $ "Undefined case: " ++ show x

transTokUnit :: AbsParser.TokUnit -> Result
transTokUnit x = case x of
  AbsParser.TokUnit string -> failure x

transUIdent :: AbsParser.UIdent -> String 
transUIdent x = case x of
  AbsParser.UIdent string -> snd string 

transPIdent :: AbsParser.PIdent -> String
transPIdent x = case x of
  AbsParser.PIdent string -> snd string 

transPInteger :: AbsParser.PInteger -> Int 
transPInteger x = case x of
  AbsParser.PInteger string -> read (snd string)


transSCPL :: AbsParser.SCPL -> [(String,Expr)] 
transSCPL x = case x of
  AbsParser.SCPLPROG defns ->  map transDefn defns

transDefn :: AbsParser.Defn -> (String,Expr)
transDefn x = case x of
  AbsParser.DEFN pident stmt -> (transPIdent pident, transStmt stmt)

transStmt :: AbsParser.Stmt -> Expr 
transStmt x = case x of
  AbsParser.CASESTMT exp caseterms ->  let (tExpr,fExpr) = (handleCaseTerms caseterms) 
                                       in EIf (transExp exp) tExpr fExpr
  AbsParser.IFSTMT exp stmt1 stmt2 -> EIf (transExp exp) (transStmt stmt1) (transStmt stmt2)
  AbsParser.BARESTMT exp -> transExp exp
  AbsParser.ELet let_ letinstmt stmt -> let (var,expr) = transLetInStmt letinstmt 
                                            ebody = transStmt stmt
                                        in case transLet let_ of 
                                                True  -> ELet var expr ebody
                                                False -> ELet var expr ebody 


transLet :: AbsParser.Let -> Bool 
transLet x = case x of
  AbsParser.LET -> True 
  AbsParser.LRec -> False 

transCaseTerm :: AbsParser.CaseTerm -> (Bool,Expr)
transCaseTerm x = case x of
  AbsParser.CASE_STMT casepattern stmt -> (transCasePattern casepattern, transStmt stmt)

transLetInStmt :: AbsParser.LetInStmt -> (String,Expr)
transLetInStmt x = case x of
  AbsParser.LET_IN_STMT pident exp -> (transPIdent pident, transExp exp)



transCasePattern :: AbsParser.CasePattern -> Bool 
transCasePattern x = case x of
  AbsParser.TRUE_PATTERN -> True 
  AbsParser.FALSE_PATTERN -> False 


handleCaseTerms :: [AbsParser.CaseTerm] -> (Expr,Expr)
handleCaseTerms [x,y] = let xpair = transCaseTerm x 
                            ypair = transCaseTerm y 
                        in if fst xpair == True then (snd xpair,snd ypair) else (snd ypair,snd xpair) 

transExp :: AbsParser.Exp -> Expr 
transExp x = case x of
  AbsParser.EInt pinteger -> EInt (transPInteger pinteger)
  AbsParser.ETrue -> EBool True
  AbsParser.EFalse -> EBool False
  AbsParser.EVar pident -> EVar (transPIdent pident)
  AbsParser.EString string -> EStr string
  AbsParser.EList exps -> EList (map transExp exps)-- foldr (\x y -> App (App (Var "cons") x) y) (Var "nil") (map transExp exps)  
  -- AbsParser.ECall pident exps -> foldl EApp (EVar (transPIdent pident)) (map transExp exps) -- App (Var (transPIdent pident)) (map transExp exps)  -- App Expr [Expr] 
  AbsParser.ENeg exp -> EOp (EInt 0) Sub (transExp exp) 
  AbsParser.CONSTERM exp1 exp2 -> EApp (EApp (EVar "cons") (transExp exp1)) (transExp exp2)
  AbsParser.EAPPEND exp1 exp2 -> EOp (transExp exp1) Append (transExp exp2)
  AbsParser.EMul exp1 exp2 -> EOp (transExp exp1) Mul (transExp exp2)
  AbsParser.EDiv exp1 exp2 -> EOp (transExp exp1) Div (transExp exp2)
  AbsParser.EAdd exp1 exp2 -> EOp (transExp exp1) Add (transExp exp2)
  AbsParser.ESub exp1 exp2 -> EOp (transExp exp1) Sub (transExp exp2)
  AbsParser.ELt exp1 exp2 ->  EOp (transExp exp1) Lt (transExp exp2)
  AbsParser.EGt exp1 exp2 ->  EOp (transExp exp1) Gt (transExp exp2)
  AbsParser.ELEq exp1 exp2 -> EOp (transExp exp1) LEq (transExp exp2)
  AbsParser.EGEq exp1 exp2 -> EOp (transExp exp1) GEq (transExp exp2)
  AbsParser.EEq exp1 exp2 ->  EOp (transExp exp1) Eq (transExp exp2)
  AbsParser.ENEq exp1 exp2 -> EOp (transExp exp1) NEq (transExp exp2)
  AbsParser.EAnd exp1 exp2 -> EOp (transExp exp1) And (transExp exp2)
  AbsParser.EOr exp1 exp2 -> EOp (transExp exp1) Or (transExp exp2)
  AbsParser.ELambda pidents stmt -> makeAbstractions pidents (transStmt stmt) 
  AbsParser.EApp exp1 exp2 -> EApp (transExp exp1) (transExp exp2)


makeAbstractions :: [AbsParser.PIdent] -> Expr -> Expr
makeAbstractions [] e = e
makeAbstractions (x:xs) e = ELam (transPIdent x) (makeAbstractions xs e)


-- transSCPL = undefined