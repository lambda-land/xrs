{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
module Examples where

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

data Nat
  = Zero
  | Succ Nat
  deriving (Eq)

instance Show Nat where
  show Zero = "0"
  show (Succ n) = "S " ++ show n

data LTJudge = LTJudge
  deriving (Eq, Read, Show, Typeable, Data)

instance Unifiable LTJudge where

instance Judgement (Nat,Nat) LTJudge where
  rules :: [(Nat,Nat) -> Result LTJudge]
  rules = [inc,trans]
{-
n == m
---------Inc
n < S m
-}

inc :: (Nat,Nat) -> Result LTJudge
inc (n, Succ m) | n == m = return LTJudge
inc _ = mzero


{-
n < m
--------Trans
n < S m
-}

trans :: (Nat,Nat) -> Result LTJudge
trans (n, Succ m) = do
  (n,m) .>. LTJudge
  return LTJudge
trans _ = mzero


infer' :: (Judgement i o) => i -> [(i,o)]
infer' i = do
  o <- infer i
  return (i,o)

t1 = infer' (Zero, Succ Zero)

t2 = infer' (Zero, Succ (Succ Zero))

t3 = infer' (Succ (Succ Zero), Succ (Succ (Succ (Succ Zero))))