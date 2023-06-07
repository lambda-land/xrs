{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
module TypeFV where

import Language.Rules.TypeGU
import Language.Rules.TypeGT

import Data.Generics
import Control.Monad

{-
class Unifiable o => Judgement i o | i -> o  where
	rules :: [i -> R o]

infer :: Judgement i o => i -> [o]
-}

type Result o = R o


data Expr = Var String | App Expr Expr | Lam String Expr
  deriving Show

data Free = Free
  deriving (Eq, Read, Show, Typeable, Data)

instance Unifiable Free where

type FVJudge = (String,Expr,Free)

instance Judgement (String, Expr) Free where
  rules :: [(String, Expr) -> Result Free]
  rules = [var, app1, app2, lam]


{-
v == x
-------------Var
(v,x) free
-}

-- var :: MonadPlus m => (String, Expr) -> m Free
var :: (String, Expr) -> Result Free
var (v, (Var x)) | x == v = return Free
var _ = mzero

{-
(v,e1) free
---------------------App1
(v,e1 e2) free
-}

app1 :: (String,Expr) -> Result Free
app1 (v, (App e1 e2)) = do
  (v, e1) .>. Free
  return Free
app1 _ = mzero


{-
(v,e2) free
---------------------App2
(v,e1 e2) free
-}

app2 :: (String,Expr) -> Result Free
app2 (v, (App e1 e2)) = do
  (v, e2) .>. Free
  return Free
app2 _ = mzero

{-
v /= x      (v,e) free
------------------------Lam
(v,Lam x e) free
-}

lam :: (String,Expr) -> Result Free
lam (v, (Lam x e)) = do
  (v, e) .>. Free
  if v == x then mzero else return Free
lam _ = mzero


-- Examples

vx = infer ("x", (Var "x"))

vlx = infer ("x", Lam "x" (Var "x"))

vy = infer ("y", (Var "x"))

va = infer ("x", App (Lam "x" (Var "x")) (Var "x"))

vay = infer ("x", App (Lam "x" (Var "x")) (Var "y"))

