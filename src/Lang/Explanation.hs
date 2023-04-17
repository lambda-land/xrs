module Lang.Explanation where


import Lang.Lang
import Lang.Operation
import Logic.Proof
import Lang.Evaluation
import Lang.Denotation

import Data.List (intercalate,nub)

-- class Explain j where 
--   premises :: j -> [[j]]


{--

  P1    ...   Pn
  -----------------------------
    < Q | QS > 


  
  ---------------------------------------------
    < D, rho |- e => v | e' => v' >


findExp :: Proof j -> [j]
findExp (Node Q [P1,...,Pn]) = QS

--}



{--

Variable capturing rule:    D, rho : e ~> e'
    where e' is the expression e, with all non closures or global functions substituted for their names.


(x,v) in rho    v /= (closure y -> e) 
-----------------------------------------FillVal
D, rho : x ~> v


------------------FillName
D, rho : x ~> x


D, rho : e1 ~> e1'    D, rho : e2 ~> e2'
-----------------------------------------FillOp
D, rho : e1 op e2 ~> e1' op e2'


D, rho' : e ~> e'    rho' = rho \\ x
-------------------------------------------FillLam
D, rho : fun x -> e ~> fun x -> e'


D, rho : e1 ~> e1'     D, rho : e2 ~> e2'
--------------------------------------------FillApp
D, rho : e1 e2 ~> e1' e2'


D, rho : e1 ~> e1'     D, rho : e2 ~> e2'
------------------------------------------------------FillLet
D, rho : let x = e1 in e2 ~> let x = e1' in e2'


D, rho : ei ~> ei'
----------------------------------------------FillList
D, rho : [e1, ..., en] ~> [e1', ..., en']

--}

{--

  ----------------------------XLit
    < D, rho |- v => v | [] >
  


  ----------------------------XVar
    < D, rho |- x => v | [] >



   D, rho |- e1 => v1       D, rho |- e2 => v2       v1 + v2 = v     
   D, rho : e1 ~> e1'     D, rho : e2 ~> e2'
  ------------------------------------------------------------------XAdd
    < D, rho |- e1 + e2 => v | e1' + e2' => v >



    D, rho |- e1 => v1          v1 = (closure z -> e',rho')      D, rho[x |-> v1] |- e2 => v2
    D, rho : e1 ~> e1'          D, rho[x |-> v1] : e2 ~> e2'
  ---------------------------------------------------------------------XLetFun
    < D, rho |- let x = e1 in e2 => v | e2' => v >


    D, rho |- e1 => v1      D, rho[x |-> v1] |- e2 => v     
    D, rho : e1 ~> e1'     D, rho[x |-> v1] : e2 ~> e2'
  -----------------------------------------------------------------XLet
    < D, rho |- let x = e1 in e2 => v | e1' => v1, e2' => v >



    D, rho |- e1 = (closure x -> e', rho')           < D, rho |- e2 => v2 | Delta >     D, rho'[x |-> v2] |- e' => v
    D, rho : e1 ~> e1'           D, rho : e2 ~> e2'
  ---------------------------------------------------------------------------------------------------------------------XApp
    < D, rho |- e1 e2 => v | e1' v2 => v, e2' => v2, Delta >


    D, rho |- ei => vi     D, rho : ei ~> ei'     f(v1,...,vn) = v
  ---------------------------------------------------------------------XBuiltin
    < D, rho |- f e1 ... en => v | f e1' ... en' => v >


    D, rho |- e1 => True        D, rho |- e2 => v
    D, rho : e1 ~> e1'        D, rho : e2 ~> e2'
  ------------------------------------------------------------------------XIfTrue
    < D, rho |- if e1 then e2 else e3 => v | e1' => True, e2' => v >


    D, rho |- e1 => False        D, rho |- e3 => v
    D, rho : e1 ~> e1'        D, rho : e3 ~> e3'
  ------------------------------------------------------------------------XIfFalse
    < D, rho |- if e1 then e2 else e3 => v | e1' => True, e3' => v >


--}






















-- data EvalJ = EvalJ GlobalEnv LocalEnv Expr Val
data XEvalJ = XEvalJ Expr Val deriving Eq

getParts :: Proof EvalJ -> (Expr, Val)
getParts (Node (EvalJ d rho e v) ps) = (e, v)



findExp :: Proof EvalJ -> [XEvalJ]
findExp (Node (EvalJ d rho e v) ps) = case (e,v, map conclusion ps) of
{--
  ----------------------------XLit
    < D, rho |- v => v | [] >
--}
  (EInt i, VInt i',[])   -> []
  (EBool b, VBool b',[]) -> []
  (EChar c, VChar c',[]) -> []
  (EStr s, VStr s',[])   -> []
  (EList es, VList vs,_) -> []
{--
  ----------------------------XVar
    < D, rho |- x => v | [] >
--}
  (EVar x, v,[])         -> []
{--
   D, rho |- e1 => v1       D, rho |- e2 => v2       v1 + v2 = v     
   D, rho : e1 ~> e1'     D, rho : e2 ~> e2'
  ------------------------------------------------------------------XAdd
    < D, rho |- e1 + e2 => v | e1' + e2' => v >
--}
{--
  (EOp e1 op e2, v, [EvalJ _ _ e1p v1, EvalJ _ _ e2p v2]) -> [XEvalJ (EOp e1' op e2') v]
    where e1' = fillEnv rho e1
          e2' = fillEnv rho e2
--}
  (EOp e1 op e2, v, [EvalJ _ _ e1p v1, EvalJ _ _ e2p v2]) -> [XEvalJ (EOp e1' op e2') v] ++ greeks
    where e1' = fillEnv rho e1
          e2' = fillEnv rho e2
          greeks = concatMap findExp ps
{--
    D, rho |- e1 => v1          v1 = (closure z -> e',rho')      D, rho[x |-> v1] |- e2 => v2
    D, rho : e1 ~> e1'          D, rho[x |-> v1] : e2 ~> e2'
  ---------------------------------------------------------------------XLetFun
    < D, rho |- let x = e1 in e2 => v | e2' => v >
--}
  (ELet x e1 e2, v, [EvalJ _ _ e1p (VClo _ _ _), EvalJ _ rho' e2p v2]) -> [XEvalJ e2' v]
    where e1' = fillEnv rho e1
          e2' = fillEnv rho' e2
{--
    D, rho |- e1 => v1      D, rho[x |-> v1] |- e2 => v     
    D, rho : e1 ~> e1'     D, rho[x |-> v1] : e2 ~> e2'
  -----------------------------------------------------------------XLet
    < D, rho |- let x = e1 in e2 => v | e1' => v1, e2' => v >
--}
  (ELet x e1 e2, v, [EvalJ _ _ e1p v1, EvalJ _ rho' e2p v2]) -> [XEvalJ e1' v1, XEvalJ e2' v]
    where e1' = fillEnv rho e1
          e2' = fillEnv rho' e2
{-- 
    D, rho |- e1 = (closure x -> e', rho')           < D, rho |- e2 => v2 | Delta >     rho'[x |-> v2] |- e' => v
    D, rho : e1 ~> e1'           D, rho : e2 ~> e2'
  ---------------------------------------------------------------------------------------------------------------------XApp
    < D, rho |- e1 e2 => v | e1' v2 => v, e2' => v2, Delta, Sigma >
--}
{--
  (EApp e1 e2, v, [EvalJ _ _ e1p (VClo _ _ _), j@(EvalJ _ _ e2p v2), j'@(EvalJ _ _ _ _)]) -> [XEvalJ (EApp e1' (embed v2)) v, XEvalJ e2' v2] ++ delta ++ sigma
    where e1' = fillEnv rho e1
          e2' = fillEnv rho e2
          delta = findExp (head $ filter ((==j) . conclusion) ps)
          sigma = -- findExp (ps !! 2)
--}
  (EApp e1 e2, VClo _ _ _, [EvalJ _ _ e1p (VClo _ _ _), EvalJ _ _ e2p v2, EvalJ _ _ _ _]) -> [XEvalJ e2' v2] ++ greeks
    where e1' = fillEnv rho e1
          e2' = fillEnv rho e2
          greeks =  concatMap findExp (take 1 ps) -- findExp (ps !! 0) -- [] -- findExp (ps !! 1) -- concatMap findExp ps
  (EApp e1 e2, v, [EvalJ _ _ e1p (VClo _ _ _), EvalJ _ _ e2p v2, EvalJ _ _ _ _]) | [] <- findExp (ps !! 1) -> greeks
    where e1' = fillEnv rho e1
          e2' = fillEnv rho e2
          greeks = concatMap findExp ps 

  (EApp e1 e2, v, [EvalJ _ _ e1p (VClo _ _ _), EvalJ _ _ e2p v2, EvalJ _ _ _ _]) -> [XEvalJ (EApp e1' (embed v2)) v, XEvalJ e2' v2] ++ greeks
    where e1' = fillEnv rho e1
          e2' = fillEnv rho e2
          greeks = concatMap findExp (take 2 ps)
{--
    D, rho |- ei => vi      D, rho : ei ~> ei'      f(v1,...,vn) = v
  ---------------------------------------------------------------------XBuiltin
    < D, rho |- f e1 ... en => v | f v1 ... vn => v, ei' => vi >
--}
  (EApp e1 e2, v, ps') -> [XEvalJ e' v] ++ (concatMap findExp ps)
    where exPrems = [XEvalJ ei' vi | (EvalJ d rho ei vi) <- ps', let ei' = fillEnv rho ei]
          vis     = [vi | (XEvalJ _ vi) <- exPrems]
          e'      = unflattenApp e1 (map embed vis)
          exps    = if null $ exPrems then [] else [XEvalJ e' v] ++ exPrems
    -- <D, rho |- tail xs | tail [1,2,3] => [2,3]>
{--
    D, rho |- e1 => True        D, rho |- e2 => v
    D, rho : e1 ~> e1'        D, rho : e2 ~> e2'
  ------------------------------------------------------------------------XIfTrue
    < D, rho |- if e1 then e2 else e3 => v | e1' => True, e2' => v >
--}
{--
  (EIf e1 e2 e3, v,[EvalJ _ _ _ (VBool True), EvalJ _ _ _ _]) -> [XEvalJ e1' (VBool True), XEvalJ e2' v]
    where e1' = fillEnv rho e1
          e2' = fillEnv rho e2
--}
  (EIf e1 e2 e3, v,[EvalJ _ _ _ (VBool True), EvalJ _ _ _ _]) -> [XEvalJ e1' (VBool True)] ++ delta
    where e1' = fillEnv rho e1
          delta = findExp (ps !! 1)
{--
    D, rho |- e1 => False        D, rho |- e3 => v
    D, rho : e1 ~> e1'        D, rho : e3 ~> e3'
  ------------------------------------------------------------------------XIfFalse
    < D, rho |- if e1 then e2 else e3 => v | e1' => True, e3' => v >
--}
{--
  (EIf e1 e2 e3, v,[EvalJ _ _ _ (VBool False), EvalJ _ _ _ _]) -> [XEvalJ e1' (VBool False), XEvalJ e3' v]
    where e1' = fillEnv rho e1
          e3' = fillEnv rho e3
--}
  (EIf e1 e2 e3, v,[EvalJ _ _ _ (VBool False), EvalJ _ _ _ _]) -> [XEvalJ e1' (VBool False)] ++ delta
    where e1' = fillEnv rho e1
          delta = findExp (ps !! 1)

-- rho |- if e1 then e2 else e3 -------------> < D, rho |- if e1 then e2 else e3 => v | e1' => True, e3' => v >


  (e,VClo _ _ _,_) -> []

  -- (e,v,_) -> [XEvalJ e v]
  _                   -> error "findExp: literal mismatch"


data XTag = XTag EvalJ [XEvalJ]

tagJudge :: EvalJ -> XTag
tagJudge j = XTag j (findExp (prove' j))

tagJudge' :: Proof EvalJ -> XTag
tagJudge' p = XTag (conclusion p) (findExp p)

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