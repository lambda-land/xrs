module Lang.LiftedLet where


import Lang.Lang

import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map


import Logic.Proof
import Lang.Operation
import Lang.Evaluation


import Debug.Trace
import Lang.Classification
import Lang.ClassificationInstances ()

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
bindingsToLet m e | [] <- Map.toList m = e
                  | otherwise          = foldr (\ (k,e') e -> ELet ("tmp" ++ show k) e' e) e' (init (Map.toList m))
  where e' = evalFactor e

constructLet :: Expr -> Expr
constructLet e = bindingsToLet (execFactor e) e


constructLetFromState :: Expr -> FactorState Expr
constructLetFromState e = do 
  bindings <- get
  return $ bindingsToLet bindings e


  -- let (e',m) = runFactor e
  -- in return $ bindingsToLet m e'


liftedLetProofTree :: Expr -> Proof EvalJ
liftedLetProofTree = fmap fillEnvJ . fmap fillEnvJ . traceExpr . constructLet 

{-
moreLiftedLets :: Proof EvalJ -> Proof EvalJ
moreLiftedLets (Proof j ps)  = Proof j (map moreLiftedLets $ children liftedPT)
  where liftedPT = fmap (fillEnvJ . fillEnvJ) (suppose (EvalJ d rho (constructLet e) v))
        (EvalJ d rho e v) = j
-}

branchMap :: (a -> FactorState b) -> [a] -> FactorState [b]
branchMap f [] = return []
branchMap f (x:xs) = do
  s <- get
  x' <- f x
  put s
  xs' <- branchMap f xs
  return $ x':xs'


moreLiftedLets :: Proof EvalJ -> FactorState (Proof EvalJ)
moreLiftedLets (Proof j []) = return $ Proof j []
moreLiftedLets (Proof j ps) | isLiftedLetJ j = do
  ps' <- branchMap moreLiftedLets ps
  return $ Proof j ps'
moreLiftedLets (Proof j ps) = do
  traceShowId j `seq` return ()
  (EvalJ d rho e v) <- return j
  e' <- factor e
  e'' <- constructLetFromState e'
  let liftedPT = fmap (fillEnvJ . fillEnvJ) (suppose (EvalJ d rho e'' v))
  let j' = conclusion liftedPT
  traceShowId j' `seq` return ()
  moreLiftedLets (Proof j' ps)
  -- ps' <- mapM moreLiftedLets ps
  -- return $ Proof j' ps'



isLiftedLetJ :: EvalJ -> Bool
isLiftedLetJ (EvalJ _ _ (ELet ('t':'m':'p':_) _ _) _) = True
isLiftedLetJ _ = False

extract :: Proof EvalJ -> [EvalJ]
extract (Proof j ps) | isLiftedLetJ j = concatMap extract ps
                     | otherwise = return j


data Originality j = Synthetic j | Original j
  deriving Show

unoriginal (Synthetic j) = j
unoriginal (Original j) = j

instance Classification (Originality EvalJ) EvalJ () where
  classify () j _ | isSynthetic j = Synthetic j
                  | otherwise = Original j
    where isSynthetic = isLiftedLetJ


annotateOriginality :: Expr -> Proof (Originality EvalJ)
annotateOriginality j = fmap fst $ annotate @(Originality EvalJ) @EvalJ @() $ liftedLetProofTree j

selectOriginal :: Proof (Originality EvalJ) -> [EvalJ]
selectOriginal = map unoriginal . filter originality . toList'
  where originality (Original j) = True
        originality _ = False



newtype FirstOriginalCtx = FirstOriginalCtx Bool
  deriving Show

-- Keeps tags judgmenets if they are the first original judgement when traversing down.
instance Context FirstOriginalCtx EvalJ where
  rootCtx _ = FirstOriginalCtx False
  childContexts (FirstOriginalCtx False) (Proof j ps) | isLiftedLetJ j = [FirstOriginalCtx (not $ isLiftedLetJ j') | j' <- map conclusion ps]
  childContexts (FirstOriginalCtx _) (Proof j ps) = map (const $ FirstOriginalCtx False) ps



exmp = parseExample "add (id 2 + id 3) (id 6)"
-- exmp = parseExample "add 2 3"

exmp1 = extract $ liftedLetProofTree $ parseExample "add (id 2) (id 3)"
exmp2 = extract $ liftedLetProofTree $ parseExample "id (add 2) 5" -- closure names not being filled in with tmp vars

exmp3 = extract $ liftedLetProofTree $ parseExample "length (filter odd [1,2,3,4,5])"

exmp4 = hidePast 2 $ liftedLetProofTree $ parseExample "fac 5"


st = moreLiftedLets $ traceExpr $ parseExample "add (id 2) (id 3)"