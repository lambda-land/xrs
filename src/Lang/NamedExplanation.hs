{-# LANGUAGE ViewPatterns #-}
module Lang.NamedExplanation where


import Lang.Lang
import Lang.Operation
import Logic.Proof
import Lang.Evaluation
import Lang.Denotation

import Data.List (intercalate,nub)





data XEvalJ = XEvalJ Expr Val deriving Eq

getParts :: Proof EvalJ -> (Expr, Val)
getParts (Node (EvalJ d rho e v) ps) = (e, v)


oneStep :: Proof a -> (a,[a])
oneStep (Node j ps) = (j, map (conclusion) ps)


subTreeByJudge :: Eq j => j -> Proof j -> Proof j
subTreeByJudge j (Node _ ps) = head $ filter ((j==) . conclusion) ps


fillRight :: Proof EvalJ -> [XEvalJ]
fillRight p =
  case oneStep p of
{--
  -------------------------------XLit
  < D, rho |- v => v | [] >
--}
    (EvalJ _ _ (EInt i) (VInt i'), []) -> []
    (EvalJ _ _ (EBool b) (VBool b'), []) -> []
    (EvalJ _ _ (EStr s) (VStr s'), []) -> []
    (EvalJ _ _ (EChar c) (VChar c'), []) -> []

{--
  ----------------------------XLocalVar
    < D, rho |- x => v | [] >
--}
    (EvalJ _ rho (EVar x) v, []) | (x,v) `elem` rho -> []


{--
  (x,e) in D     < D, [] |- e => (closure z -> e', rho', ns) | _ >
  ----------------------------------------------------------XGlobalVarClosure
  < D, rho |- x => (closure z -> e', rho', x:ns) | [] > 
--}
    (EvalJ d rho (EVar x) v, _) | x `elem` map fst d -> []

{--
  (x,e) in D       < D, {} |- e => v | Gamma >     v /= closure
  -------------------------------XGlobalVarNoClosure
  < D, rho |- x => v | [] >
--}
    (EvalJ d rho (EVar x) v, _) | x `elem` map fst d -> []


{--
  < D, rho |- e1 => (closure z -> e, rho, n1:_) | G1 >
  < D, rho |- e2 => v2 | G2 >          v2 = (closure _ -> _ , _ , n2:_)
  < D, rho'[z |-> v2] |- e => (closure y -> e', rho'', ns) | _ >
  -------------------------------------------------------------------------------------XAppClosure1
  < D, rho |- e1 e2 => (closure y -> e', rho'', (n1 n2):ns) = v3 | G1, G2, (n1 n2) => v3 > 
--}
    (EvalJ d rho (EApp e1 e2) v3@(VClosure _ _ _ (n':ns)), [j1,j2@(EvalJ _ _ _ (VClosure {})),_])
      -> let g1 = fillRight (subTreeByJudge j1 p)
             g2 = fillRight (subTreeByJudge j2 p)
          in g1 ++ g2 ++ [XEvalJ n' v3]


{--
  < D, rho |- e1 => (closure z -> e, rho', (n:_)) | G1 >
  < D, rho |- e2 => v2 | G2 >        v2 /= closure
  < D, rho'[z |-> v2] |- e => (closure y -> e', rho'', ns) | _ >
  ------------------------------------------------------------------------------------XAppClosure2
  < D, rho |- e1 e2 => (closure y -> e', rho'', (n e2):ns) = v3 | G1, G2, n e2 => v3 >
--}
    (EvalJ d rho (EApp e1 e2) v3@(VClosure _ _ _ (n':_)),[j1,j2,_])
      -> let g1 = fillRight (subTreeByJudge j1 p)
             g2 = fillRight (subTreeByJudge j2 p)
          in g1 ++ g2 ++ [XEvalJ n' v3]


{--
  < D, rho |- e1 => (closure z -> e, rho', (n:_)) | G1 >
  < D, rho |- e2 => v2 | G2 >
  < D, rho'[z |-> v2] |- e => v3 | _ >
  ----------------------------------------------------------XAppNoClosure
  < D, rho |- e1 e2 => v3 | G1 , G2, (n e2) => v3 >
--}

    (EvalJ d rho (EApp e1 e2) v,[j1@(EvalJ _ _ e1' (VClosure _ _ _ (n:_))),j2,_]) 
      -> let g1 = fillRight (subTreeByJudge j1 p)
             g2 = fillRight (subTreeByJudge j2 p)
          in g1 ++ g2 ++ [XEvalJ (EApp e1 e2) v]


    (_,_) -> []






data XTag = XTag EvalJ [XEvalJ]

tagJudge :: EvalJ -> XTag
tagJudge j = XTag j (fillRight (prove' j))

tagJudge' :: Proof EvalJ -> XTag
tagJudge' p = XTag (conclusion p) (fillRight p)

tagProof :: Proof EvalJ -> Proof XTag
tagProof p = Node (tagJudge' p) (map tagProof (children p))


instance Show XEvalJ where
  show (XEvalJ e v) = show e ++ " => " ++ show v

instance Show XTag where
  show (XTag j []) = "..."
  show (XTag j xs) = "< " ++ show j ++ " | " ++ (intercalate ", " $ map show $ nub xs) ++ " >"

-- instance Show XTag where
--   show (XTag j []) = "..."
--   show (XTag j xs) = intercalate ", " $ map show xs



-- It is the case that `j`, because
-- display (tagProof $ proof j)...

-- pf = taggedProof (length [1,2,3,4,5] => 5)
-- display pf = [1 + length [2,3,4,5] => 5, tail [1,2,3,4,5] => [2,3,4,5]]

-- display :: Proof XTag -> [XEvalJ]
-- display (Node (XTag j xs) _) = xs


rightProofTree :: Proof XTag -> Proof [XEvalJ]
rightProofTree (Node (XTag j xs) cs) = Node xs (map rightProofTree cs)







-- Two options: modify app rule, or do post-processing. < length ([1, 2, 3, 4, (3 + 9)]) => 5 | length ([1, 2, 3, 4, 12]) => 5 >
-- App rule is correct in the sense that it handles expressions of tthe form e1 (e2 ... en), but not e1 e2. 







--


-- 
-- length [1,2,3,4,5] => 5

-- 
-- 1 + length [2,3,4,5] => 5, tail [1,2,3,4,5] => [2,3,4,5]
-- 
-- 1 + length (tail [1,2,3,4,5]) => 5, tail [1,2,3,4,5] => [2,3,4,5]

-- length (tail [1,2,3,4,5]) => 4
-- length [2,3,4,5] => 4


-- length (tail (tail [1,2,3,4,5])) => 3

-- tail [1,2,3,4,5] => [2,3,4,5], tail [2,3,4,5] => [3,4,5], length [3,4,5] => 3


-- inc (add (add 10 20) (add 30 40))



-- class Explain j => Tagged j a where
--   explain :: j -> [a] 



-- class Explain j , Tagged j a => Display xs where
--   display 

-- data Tag = Tag { tag :: String, exps :: [Tag] } deriving (Show, Eq)
















{--
  < D, [x -> 6] |- fac (fac (fac x)) | fac 720 => ..., fac 6 => 720, fac 3 => 6 >

  f (g (h i)) 

-------------------------------

    D, rho |- e1 = (closure x -> e', rho')           D, rho |- e2 => v2     D, rho'[x |-> v2] |- e' => v
    D, rho : e1 ~> e1'           D, rho : e2 ~> e2'
  -----------------------------------------------------------------------------------------------------XApp
    < D, rho |- e1 e2 => v | e1' v2 => v, e2' => v2 >

    < D, rho |- e1 v2 => v | _ >      < D, rho |- e2 e3 => v2 | Delta >
    D, rho : e1 ~> e1'      D, rho : e2 ~> e2'      D, rho : e3 ~> e3'
  ------------------------------------------------------------------------
    < D, rho |- e1 (e2 e3) => v | e1' v2 => v, e2' e3' => v2, Delta > 

-------------------------------


    tail xs 


    < D, [xs |-> [1,2,3,4]] |- length (tail xs) => 3 | length [2,3,4] => 3, tail [1,2,3,4] => [2,3,4] >

    < D, [xs |-> [1,2,3,4]] |- fac (length (tail xs)) => 6 | fec 3 => 6, length [2,3,4] => 3, tail [1,2,3,4] => [2,3,4] >



  < D, [x -> 5, y -> 3] |- (f x) y => 8 | (f 5) 3 => 8, 3 => 3 >

  
--}



{--
    D, [] |- let x = fac 3 in x + x => 12

    D, [] |- fac 3 => 6         D, [x |-> 6] |- x + x => 12 
    D, [] : fac 3 => fac 3          D, [x |-> 6] : x + x ~> 6 + 6 
-----------------------------------------------------------------------------
    < D, [] |- let x = fac 3 in x + x => 12 | fac 3 => 6, 6 + 6 => 12 > 
--}



evaluationExamples :: [XTag]
evaluationExamples = map (conclusion . tagProof . traceExample) examples
  where examples = [ "length [10,20,30,40,50]"
                   , "length (tail [10,20,30,40,50])"
                   , "length (tail (tail [10,20,30,40,50]))"
                   , "add (4 + 5) (6 + 7)"
                   , "add (add 4 5) (add 6 7)"
                   , "add (id 1) 2"
                   , "id add 1 2"
                   ]


{--

< length ([10, 20, 30, 40, 50]) => 5 | ([10, 20, 30, 40, 50] == []) => False, (1 + length (tail ([10, 20, 30, 40, 50]))) => 5, length ([20, 30, 40, 50]) => 4, tail ([10, 20, 30, 40, 50]) => [20, 30, 40, 50] >
< length (tail ([10, 20, 30, 40, 50])) => 4 | length ([20, 30, 40, 50]) => 4, tail ([10, 20, 30, 40, 50]) => [20, 30, 40, 50] >
< length (tail (tail ([10, 20, 30, 40, 50]))) => 3 | length ([30, 40, 50]) => 3, tail (tail ([10, 20, 30, 40, 50])) => [30, 40, 50], tail ([20, 30, 40, 50]) => [30, 40, 50], tail ([10, 20, 30, 40, 50]) => [20, 30, 40, 50] >
< add ((4 + 5)) ((6 + 7)) => 22 | add ((4 + 5)) 13 => 22, (6 + 7) => 13, (4 + 5) => 9 >
< add (add 4 5) (add 6 7) => 22 | add (add 4 5) 13 => 22, add 6 7 => 13, add 4 5 => 9, 4 => 4, (4 + 5) => 9, 6 => 6, (6 + 7) => 13 >
< add (id 1) 2 => 3 | id 1 => 1, (1 + 2) => 3 >
< id add 1 2 => 3 | 1 => 1, add => (closure x -> (fun y -> (x + y))), (1 + 2) => 3 >




< length (tail (tail ([10, 20, 30, 40, 50]))) => 3 | 
tail ([10, 20, 30, 40, 50]) => [20, 30, 40, 50],
tail ([20, 30, 40, 50]) => [30, 40, 50],          
length ([30, 40, 50]) => 3
>

< add (id 1) 2 => 3 | 
id 1 => 1,
add 1 2 => 3
>

f x = length (tail x)

< f [5,6,7] => 2 | f [5,6,7] => 2 >
< length (tail [5,6,7]) => 2 | tail [5,6,7] => [6,7], length [6,7] => 2 >
< id add 1 2 => 3 | id add 1 2 => 3 >
< id add 1 2 => 3 | id add => add, add 1 2 => 3 > -- preferred

< add (add 2 3) (add 4 5) => 14 | add (add 2 3) 9 => 14, add 4 5 => 9 >

< add (add 2 3) (add 4 5) => 14 | add 5 9 => 14, add 4 5 => 9, add 2 3 => 5 >


--------------------------------------------------
< e1 e2 => v | e1 v2 => v, e2 => e2, Delta >




< f [5,6,7] => 2 | f [5,6,7] => 2 >
< length (tail [5,6,7]) => 2 | tail [5,6,7] => [6,7], length [6,7] => 2 >
< id add 1 2 => 3 | id add 1 2 => 3, add 1 => ? >
< id add 1 2 => 3 | id add => add, add 1 2 => 3, add 1 => ? >
< add 1 2 => 3 | add => (closure x -> (fun y -> x + y)), add 1 => (closure y -> 1 + y), add 1 2 => 3 >
< add (add 2 3) (add 4 5) => 14 | add (add 2 3) 9 => 14, add 4 5 => 9 >


< f v1 v2 => w | f v1 v2 => w >
< f (e1 e2) v2 => w | e1 e2 => v1, f v1 v2 => w >

< add (add 2 3) (add 4 5) => 14 | add 5 9 => 14, add 4 5 => 9, add 2 3 => 5 >





------------------------------------------------------------------------------ Apr 12
< length (tail (tail ([10, 20, 30, 40, 50]))) => 3 | 
tail ([10, 20, 30, 40, 50]) => [20, 30, 40, 50],
tail ([20, 30, 40, 50]) => [30, 40, 50],          
length ([30, 40, 50]) => 3
>

< add (id 1) 2 => 3 | 
id 1 => 1,
add 1 2 => 3
>

< add (add 2 3) (add 4 5) => 14 | add 5 9 => 14, add 4 5 => 9, add 2 3 => 5 >


--}