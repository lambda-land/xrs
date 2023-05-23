{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Lang.Heuristic where

import Data.List (sortBy,sortOn)

import Logic.Proof


import Lang.Operation
import Lang.Lang
import Data.Data (Proxy)

{-
  class Heuristic h j | h -> j where
    score :: h -> Float
    assign :: j -> [Proof (h,j)] -> h

  annotate :: Heuristic h j => Proof j -> Proof (h,j)
-}

{-




class Context c j => Classify h j c | h -> j c where
  -- The measure of the heuristic value.
  -- Compute the heuristic value for every node in the proof tree based on a context
  classify :: c -> j -> [Proof (h,j)] -> h

class Context c j where
  rootCtx :: c
  -- Compute the child contexts for a node in the proof tree
  childContexts :: c -> Proof j -> [c]


-- sml, spj textbook




instance Context () j where
  rootCtx = ()
  childContexts _ (Proof j ps) = [() | _ <- ps]

instance (Context a j, Context b j) => Context (a, b) j where
  rootCtx = (rootCtx, rootCtx)
  childContexts (a, b) n = zip (childContexts a n) (childContexts b n)

instance (Heuristic h1 j, Heuristic h2 j) => Heuristic (h1,h2) j where
  score (h1,h2) = score h1 + score h2
  assign (c1,c2) j ps = (assign c1 j ps1, assign c2 j ps2) where
    ps1 = map (fmap (\((h1, _), j) -> (h1, j))) ps
    ps2 = map (fmap (\((_, h2), j) -> (h2, j))) ps

-}





{-
simpleAnnotate :: (Heuristic h j ()) => Proof j -> Proof (h,j)
simpleAnnotate (Node j ps) = Node (assign j ps', j) ps'
  where ps' = map simpleAnnotate ps

genAnnotate :: (Heuristic h j c) => Proof j -> Proof (h,j)
genAnnotate = go initContext 
  where go ctx n@(Node j ps) = Node (assign ctx j ps', j) ps'
          where ctxs' = childContexts ctx n
                ps' = zipWith go ctxs' ps

-- class GenHeuristic h j | h -> j where
--   type Context
--   genScore :: h -> Float
--   genAssign :: Context -> j -> [Proof (h,j)] -> (h, [Context])
--   initContext :: Context
--   -- annotate :: Proof j -> Proof (h,j)

-- instance Heuristic h j => GenHeuristic h j where
--   type Context = ()
--   genScore = score
--   genAssign () j ps = (assign j ps, [() | _ <- ps])
--   initContext = ()
--   -- annotate = annotateRec assign

annotateRec :: (j -> [Proof (h,j)] -> h) -> Proof j -> Proof (h,j)
annotateRec assign (Node j ps) = Node (assign j ps', j) ps'
  where ps' = map (annotateRec assign) ps


select :: forall h j. Heuristic h j => Proxy h -> Int -> Proof j -> [j]
select _ n = select' n . annotate @h


select' :: Heuristic h j => Int -> Proof (h,j) -> [j]
select' n pf = take n $ map snd $ sortOn (score . fst) (toList' pf)
  where compare' (h1,_) (h2,_) = compare (score h1) (score h2)

-- select @MyHeuristic
-- select @TrivialH Proxy 3 $ traceExample "add (id 1) 2"
-- select (Proxy @TrivialH) 3 $ traceExample "add (id 1) 2"
-- select (Proxy @(TrivialH,ClosureH)) 3 $ traceExample "add (id 1) 2"



select'' :: Classify c j h => (h -> Float) -> Proof j -> [j]
select'' = undefined 

newtype TrivialH = TH Float

instance Classify TrivialH EvalJ () where
  classify :: () -> EvalJ -> [Proof (TrivialH, EvalJ)] -> TrivialH
  classify _ (EvalJ _ _ e _) _ = if isTrivial e then TH 1 else TH 0
    where isTrivial (EInt _) = True
          isTrivial (EBool _) = True
          isTrivial (EStr _) = True
          isTrivial (EChar _) = True
          isTrivial (EList xs) = all isTrivial xs
          isTrivial _ = False




newtype ClosureH = CH Float

instance Heuristic ClosureH EvalJ () where
  score (CH s) = s
  assign (EvalJ _ _ _ v) _ | VClosure _ _ _ _ <- v = CH 1.0
                          | otherwise             = CH 0.0

-- combine ClosureH and TrivialH





-- doesn't work for functions like
-- fac = fun n -> if n == 0 then 1 else n * (id fac) (n-1)
doesOccurAgain :: Var -> Proof EvalJ -> Bool
doesOccurAgain n (Node (EvalJ _ _ (EApp (EVar n') _) _) ps) | n == n' = True
doesOccurAgain n (Node _ ps) = any (doesOccurAgain n) ps

newtype BaseCaseH = BHC Float 

instance Heuristic BaseCaseH EvalJ where
  score (BHC s) = s
  assign j@(EvalJ _ _ (EApp (EVar n) _) _) ps | doesOccurAgain n (fmap snd (ps !! 2)) = BHC 0.0
                                                -- builtin functions fail this test
                                              
                                              | length ps < 3 = error (show (j, map conclusion (fmap (fmap snd) ps)))
                                              | otherwise = BHC 1.0
  assign _ _ = BHC 0.0




newtype ConditionProofH = CPH Float

newtype ConditionCtx = ConditionCtx Bool

instance Context ConditionCtx where
  rootCtx = ConditionCtx False
  childContexts (ConditionCtx _) (Node (EvalJ _ _ (EIf _ _ _) _) ps) = [ConditionCtx True, ConditionCtx False]
  childContexts c (Node _ ps) = map (const c) ps



instance Heuristic TrueBranchH EvalJ ConditionCtx where
  initContext = False
  score (TBH s) = s
  assign :: Bool -> EvalJ -> [Proof (TrueBranchH, EvalJ)] -> (TrueBranchH, [Bool])
  assign (EvalJ _ _ (EIf _ _ _) _) 
  assign _ _ = CPH 0.0




-}