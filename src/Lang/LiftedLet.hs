module Lang.LiftedLet where


import Lang.Lang

import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map


import Logic.Proof
import Lang.Operation
import Lang.Evaluation



type BindingName = Int
type Bindings = Map BindingName Expr
type FactorState a = State Bindings a

mkKey :: Bindings -> BindingName
mkKey m = case Map.maxViewWithKey m of
  Nothing -> 0
  Just ((k,_),_) -> k + 1

allocate :: Expr -> FactorState BindingName
allocate e = do
  bindings <- get
  let key = mkKey bindings
  put $ Map.insert key e bindings
  return key

allocateExpr :: Expr -> FactorState Expr
allocateExpr e = do
  key <- allocate e
  return $ EVar $ "tmp" ++ show key

factor :: Expr -> FactorState Expr
factor e = case e of
  EVar _ -> return e
  Val -> return e
  ELet v e1 e2 -> do
    e1' <- factor e1
    e2' <- factor e2
    allocateExpr $ ELet v e1' e2'
  EOp e1 op e2 -> do
    e1' <- factor e1
    e2' <- factor e2
    allocateExpr $ EOp e1' op e2'
  ELam v e -> do
    e' <- factor e
    allocateExpr $ ELam v e'
  EApp e1 e2 -> do
    e1' <- factor e1
    e2' <- factor e2
    allocateExpr $ EApp e1' e2'
  EIf e1 e2 e3 -> do
    e1' <- factor e1
    e2' <- factor e2
    e3' <- factor e3
    allocateExpr $ EIf e1' e2' e3'
  EList es -> do
    es' <- mapM factor es
    allocateExpr $ EList es'
  _ -> do
    key <- allocate e
    error $ "factor: " ++ show e ++ " " ++ show key
    allocateExpr $ EVar $ show key

runFactor :: Expr -> (Expr,Bindings)
runFactor e = runState (factor e) Map.empty

execFactor :: Expr -> Bindings
execFactor = snd . runFactor

evalFactor :: Expr -> Expr
-- evalFactor = fst . runFactor
evalFactor e = case reverse $ Map.toList (execFactor e) of
  [] -> e
  ((_,e'):_) -> e'

bindingsToLet :: Bindings -> Expr -> Expr
bindingsToLet m e = foldr (\ (k,e') e -> ELet ("tmp" ++ show k) e' e) e' (init (Map.toList m))
  where e' = evalFactor e

constructLet :: Expr -> Expr
constructLet e = bindingsToLet (execFactor e) e



liftedLetProofTree :: Expr -> Proof EvalJ
liftedLetProofTree =  traceExpr . constructLet 

-- exmp = parseExample "add (id 2 + id 3) (id 6)"
exmp = parseExample "add 2 3"