module Lang.Explanation where


import Lang.Lang
import Lang.Operation
import Logic.Proof
import Lang.Evaluation
import Lang.Denotation

import Data.List (intercalate)

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
  (EOp e1 op e2, v, [EvalJ _ _ e1p v1, EvalJ _ _ e2p v2]) -> [XEvalJ (EOp e1' op e2') v]
    where e1' = fillEnv rho e1
          e2' = fillEnv rho e2
{--
    D, rho |- e1 => v1          v1 = (closure z -> e',rho')      D, rho[x |-> v1] |- e2 => v2
    D, rho : e1 ~> e1'          D, rho[x |-> v1] : e2 ~> e2'
  ---------------------------------------------------------------------XLetFun
    < D, rho |- let x = e1 in e2 => v | e2' => v >
--}
  (ELet x e1 e2, v, [EvalJ _ _ e1p (VClosure _ _ _), EvalJ _ rho' e2p v2]) -> [XEvalJ e2' v]
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
    D, rho |- e1 = (closure x -> e', rho')           < D, rho |- e2 => v2 | Delta >     D, rho'[x |-> v2] |- e' => v
    D, rho : e1 ~> e1'           D, rho : e2 ~> e2'
  ---------------------------------------------------------------------------------------------------------------------XApp
    < D, rho |- e1 e2 => v | e1' v2 => v, e2' => v2, Delta >
--}
  (EApp e1 e2, v, [EvalJ _ _ e1p (VClosure _ _ _), j@(EvalJ _ _ e2p v2), EvalJ _ _ _ _]) -> [XEvalJ (EApp e1' (embed v2)) v] ++ delta
    where e1' = fillEnv rho e1
          e2' = fillEnv rho e2
          delta = findExp (head $ filter ((==j) . conclusion) ps)
{--
    D, rho |- ei => vi      D, rho : ei ~> ei'      f(v1,...,vn) = v
  ---------------------------------------------------------------------XBuiltin
    < D, rho |- f e1 ... en => v | f v1 ... vn => v, ei' => vi >
--}
  (EApp e1 e2, v, ps') -> [XEvalJ (EApp e1 (embed v)) v] ++ [XEvalJ ei' vi | (EvalJ d rho ei vi) <- ps', let ei' = fillEnv rho ei]

    -- <D, rho |- tail xs | tail [1,2,3] => [2,3]>
{--
    D, rho |- e1 => True        D, rho |- e2 => v
    D, rho : e1 ~> e1'        D, rho : e2 ~> e2'
  ------------------------------------------------------------------------XIfTrue
    < D, rho |- if e1 then e2 else e3 => v | e1' => True, e2' => v >
--}
  (EIf e1 e2 e3, v,[EvalJ _ _ _ (VBool True), EvalJ _ _ _ _]) -> [XEvalJ e1' (VBool True), XEvalJ e2' v]
    where e1' = fillEnv rho e1
          e2' = fillEnv rho e2
{--
    D, rho |- e1 => False        D, rho |- e3 => v
    D, rho : e1 ~> e1'        D, rho : e3 ~> e3'
  ------------------------------------------------------------------------XIfFalse
    < D, rho |- if e1 then e2 else e3 => v | e1' => True, e3' => v >
--}
  (EIf e1 e2 e3, v,[EvalJ _ _ _ (VBool False), EvalJ _ _ _ _]) -> [XEvalJ e1' (VBool False), XEvalJ e3' v]
    where e1' = fillEnv rho e1
          e3' = fillEnv rho e3





  (e,VClosure _ _ _,_) -> []

  -- (e,v,_) -> [XEvalJ e v]
  _                   -> error "findExp: literal mismatch"


data XTag = XTag EvalJ [XEvalJ]

tagJudge :: Proof EvalJ -> XTag
tagJudge p = XTag (conclusion p) (findExp p)

tagProof :: Proof EvalJ -> Proof XTag
tagProof p = Node (tagJudge p) (map tagProof (children p))


instance Show XEvalJ where
  show (XEvalJ e v) = show e ++ " => " ++ show v

instance Show XTag where
  show (XTag j []) = "..."
  show (XTag j xs) = "< " ++ show j ++ " | " ++ (intercalate ", " $ map show xs) ++ " >"

-- instance Show XTag where
--   show (XTag j []) = "..."
--   show (XTag j xs) = intercalate ", " $ map show xs


--


-- class Explain j => Tagged j a where
--   explain :: j -> [a] 

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
