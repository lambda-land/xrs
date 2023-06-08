{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FunctionalDependencies #-}
module Logic.Examples where

import Logic.Rules.TypeGU
import Logic.Rules.TypeGT

import Data.Generics
import Control.Monad

import Data.List (nub, (\\))


{-
class Unifiable o => Judgement i o | i -> o  where
  rules :: [i -> R o]

infer :: Judgement i o => i -> [o]
-}


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



class Judgement i o => Composite i o j | i o -> j, j -> i o where
  composite :: i -> o -> j

infer'' :: (Composite i o j) => i -> [j]
infer'' i = do
  o <- infer i
  return (composite i o)


{- Shape Language Example -}

data Shape
  = Box
  | Shape :<: Shape
  | Shape :^: Shape
  deriving Eq

instance Show Shape where
  show :: Shape -> String
  show Box = "[]"
  show (s1 :<: s2) = "(" ++ show s1 ++ " < " ++ show s2 ++ ")"
  show (s1 :^: s2) = "(" ++ show s1 ++ " ^ " ++ show s2 ++ ")"

instance Isomorphic Int (L Int) where
  to :: Int -> L Int
  to = V
  from :: L Int -> Int
  from (V x) = x

data BBox = BBox (L Int) (L Int)
  deriving (Eq, Read, Typeable, Data)

instance Show BBox where
  show :: BBox -> String
  show (BBox w h) = show (from' w, from' h)
    where from' = from :: L Int -> Int

instance Unifiable BBox where

instance Unifiable (L Int) where


(.+.) :: L Int -> L Int -> Result (L Int)
(.+.) = bf ((+) :: Int -> Int -> Int)

max' :: L Int -> L Int -> Result (L Int)
max' = bf (max :: Int -> Int -> Int)

instance Judgement Shape BBox where
  rules :: [Shape -> Result BBox]
  rules = [box,side,above]
    where 
      box :: Shape -> Result BBox
      box Box = return (BBox (to @Int 1) (to @Int 1))
      box _ = mzero

      side :: Shape -> Result BBox
      side (s1 :<: s2) = do
        [w1,h1] <- newVars 2
        [w2,h2] <- newVars 2
        s1 .>. BBox w1 h1
        s2 .>. BBox w2 h2
        w' <- w1 .+. w2
        h' <- max' h1 h2
        return (BBox w' h')
      side _ = mzero
      
      above :: Shape -> Result BBox
      above (s1 :^: s2) = do
        [w1,h1] <- newVars 2
        [w2,h2] <- newVars 2
        s1 .>. BBox w1 h1
        s2 .>. BBox w2 h2
        w' <- max' w1 w2
        h' <- h1 .+. h2
        return (BBox w' h')
      above _ = mzero


data BBoxJudge = BBoxJudge Shape BBox

instance Show BBoxJudge where
  show (BBoxJudge s b) = show s ++ " : " ++ show b


instance Composite Shape BBox BBoxJudge where
  composite :: Shape -> BBox -> BBoxJudge
  composite = BBoxJudge



{-
instance Isomorphic (Int,Int) BBox where
  to :: (Int, Int) -> BBox
  to (w,h) = BBox w h
  from :: BBox -> (Int, Int)
  from (BBox w h) = (w,h)
-}


{-

instance Isomorphic BBox (L BBox) where
  to :: BBox -> L BBox
  to = V
  from :: L BBox -> BBox
  from (V x) = x


instance Unifiable BBox where

instance Judgement Shape BBox where
  rules :: [Shape -> Result BBox]
  rules = [box,side]
    where 
      box :: Shape -> Result BBox
      box Box = return (BBox 1 1)
      box _ = mzero

      side :: Shape -> Result BBox
      side (s1 :<: s2) = do
        [w1,h1] <- newVars 2
        [w2,h2] <- newVars 2
        s1 .>. BBox (to w1) (to h1)
        s2 .>. BBox w2 h2

        return (BBox (w1 + w2) (max h1 h2))

-}

data Expr = Var String | App Expr Expr | Lam String Expr
        deriving Show



instance Isomorphic [a] (L [a]) where
  to = V
  from (V x) = x


(.++.) = bf (++)
(.\\.) = bf (\\)
nub' = uf nub

instance Unifiable (L [String]) where

instance Judgement Expr (L [String]) where
  rules = [var, app, lam]

var (Var x) = return (to [x])
var _ = mzero

app (App e1 e2) = do
  a <- newVar
  b <- newVar
  e1 .>. a
  e2 .>. b
  (a .++. b) >>= nub' 
app _ = mzero

lam (Lam x e) = do
  a <- newVar
  e .>. a
  c <- (a .\\. (to [x]))
  return c
lam _ = mzero


-- EXAMPLES

vx = inf (Var "x")
        
vlx = inf (Lam "x" (Var "x"))

va = inf (App (Lam "x" (Var "x")) (Var "x"))
        
vay = inf (App (Lam "x" (Var "x")) (Var "y"))

vxy = inf (App (Var "x") (Var "y"))

vxx = inf (App (Var "x") (Var "x"))

