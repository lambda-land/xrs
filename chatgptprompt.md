Here is an example of an inference rule for a functional language, written in ASCII text, and its corresponding LaTeX code

The rule
```txt
    D, rho |- e1 => vi    v1 = (closure x -> e', rho')    D, rho'[x |-> v2] |- e' => v    < D, rho |- e2 => v2 | Delta >
    D, rho : e1 ~> e1'           D, rho : e2 ~> e2'
  ---------------------------------------------------------------------------------------------------------------------XApp
    < D, rho |- e1 e2 => v | e1' v2 => v, e2' => v2, Delta >
```

The latex version
```latex
\infer[\textsc{XApp}]{
	\langle D, \rho \vdash e_1 \ e_2 \Rightarrow v \ | \ e_1' \ v_2 \Rightarrow v, e_2' \Rightarrow v_2, \Delta\rangle
}{
	D, \rho  \vdash e_1 \Rightarrow v_1
	&
	(\textsf{closure} \ x \to e',\rho' ) = v_1
	&
	D, \rho'[x \mapsto v_2] \vdash e' \Rightarrow v
	&
	\langle D, \rho \vdash e_2 \Rightarrow v_2 \ | \ \Delta\rangle
	&
	D,\rho: e_1 \rightsquigarrow e_1'
	&
	D,\rho : e_2 \rightsquigarrow e_2' 
}
```

I am going to give you a list of these inference rules in ASCII, and I would like you to give me the corresponding latex source code for each. 












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



    D, rho |- ei => vi      D, rho : ei ~> ei'      f(v1,...,vn) = v
  ---------------------------------------------------------------------XBuiltin
    < D, rho |- f e1 ... en => v | f v1 ... vn => v, ei' => vi >



    D, rho |- e1 => True        D, rho |- e2 => v
    D, rho : e1 ~> e1'        D, rho : e2 ~> e2'
  ------------------------------------------------------------------------XIfTrue
    < D, rho |- if e1 then e2 else e3 => v | e1' => True, e2' => v >



    D, rho |- e1 => False        D, rho |- e3 => v
    D, rho : e1 ~> e1'        D, rho : e3 ~> e3'
  ------------------------------------------------------------------------XIfFalse
    < D, rho |- if e1 then e2 else e3 => v | e1' => True, e3' => v >

