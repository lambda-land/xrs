module Lang.Explanation where



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
