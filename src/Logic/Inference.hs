{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, UndecidableInstances #-}
module Logic.Inference where

import Logic.Rules.NDSM
import Logic.Rules.TypeGT
import Logic.Rules.TypeGU

import Logic.Proof

import Control.Monad
import Control.Applicative

import Control.Monad.Trans.State


type CoreState = (MVar, [(GS,GS)], [(GS, GFS)], Int)

type Trace i o = Branch (CoreState,[Proof (i,o)]) (o,Proof (i,o))


tryTrace :: Judgement i o => i -> [i -> Trace i o] -> Trace i o
tryTrace i (f:fx) = f i `mplus` tryTrace i fx
tryTrace i [] = mzero

liftTrace :: Judgement i o => (i -> R o) -> i -> Trace i o
liftTrace f i = mkState $ (\(s,ps) -> map (\(s',o) -> ((s',[]),(o,Proof (i,o) ps))) $ runNDSM (f i) s)
  -- (_,ps) <- fromState id
  -- (\o -> (o,Proof (i,o) ps)) <$ eval (f i)

runTrace :: Trace i o -> [Proof (i,o)]
runTrace t = map snd $ evalStateT t ((base, [], [], 1),[])

supposeTrace :: Judgement i o => i -> o -> Trace i o
supposeTrace i o = do
  mt <- tryTrace i (map liftTrace rules)
  return (o,Leaf (i,o))

-- class Judgement i o => Extractable i o j where
--   compose :: i -> o -> j
--   known :: j -> i

-- instance Extractable i o j => Explain j where
--   premises j = do
--     let i = known j
--     o <- infer i
--     return (compose i o)

-- instance Extractable i o j => Explain (i,o,j) where
--   premises (i,o,j) = infer

suppose' :: (Show i,Show o,Judgement i o) => i -> o -> Result (i,o)
suppose' expr typ = do
  incr
  mt <- try1 expr rules
  let mt' = mkGS mt
  let typ' = mkGS typ
  case (gunify mt' typ') of
    (Just x) -> do
      merge x
      onState (\(i,x,z,cnt) -> say (show i ++ " > " ++ show x ++ " > " ++ show cnt) `seq` (i,x,z,cnt+1)) 
      return (expr,mt)
    Nothing -> do {(say "mzero") `seq` mzero;}


(.>>.) :: (Show i,Show o,Judgement i o) => i -> o -> Result (i,o)
(.>>.) i o = say (show i ++ " >?> " ++ show o) `seq` f 
  where f = do
          (a,b) <- suppose' i o
          say (show a ++ " >> " ++ show b) `seq` return ()
          return (a,b)

try1 :: (Show i, Show o) => i -> [i -> R o] -> R o
try1 i (f:fx) = f i <|> try1 i fx
try1 _ [] = mzero

try1' :: i -> [i -> R o] -> R o
try1' i (f:fx) = f i <|> try1' i fx
try1' _ [] = mzero

try' :: Judgement i o => i -> R o
try' i = try1' i rules


try1Pf :: i -> [i -> R o] -> R (Proof (i,o))
try1Pf i (f:fx) = fmap (\o -> Leaf (i,o)) (f i) <|> try1Pf i fx
try1Pf _ [] = mzero

-- tries :: (Show i, Show o) => i -> [i -> R o] -> R [(i,o)]
-- tries i (f:fx) = do
--   o <- f i
--   os <- tries i fx
--   return ((i,o):os)

mkProof :: (Show i, Show o, Judgement i o) => i -> o -> Result (Proof (i,o))
mkProof i o = do
  (i',o') <- i .>>. o
  return $ Proof (i',o') []

(.|-.) :: (Show i, Show o, Judgement i o) => i -> o -> Result (Proof (i, o))
(.|-.) = mkProof


supposeProof :: (Show i,Show o,Judgement i o) => i -> o -> Result (i,o)
supposeProof expr typ = do
  incr
  mt <- try1' expr rules
  let mt' = mkGS mt
  let typ' = mkGS typ
  case (gunify mt' typ') of
    (Just x) -> merge x >> return (expr,mt)
    Nothing -> do {(say "mzero") `seq` mzero;}


{-
rule i@(i1,i2) = do 
  [o1,o2] <- newVars 2
  i1 .|-. o1
  i2 .|-. o2
  return (o1,o2)

==>

rule i@(i1,i2) = do 
  [o1,o2] <- newVars 2
  pf1 <- i1 .|-. o1
  pf2 <- i2 .|-. o2
  let o = (o1,o2)
  return (Proof (i,o) [pf1,pf2])

Proof (i,o) [pf1,pf2]

Proof (i -> o) [...]
-}

-- pfWrap :: (i -> R o) -> i -> Proof (i,o)
-- pfWrap f = Proof f []




-- proofify :: (i -> R o) -> i -> R (Proof (i,o))
-- proofify f i = do
--   o <- f i
--   return $ Proof (i,o) []

-- try1Proof :: (Show i, Show o) => i -> [i -> R o] -> R (Proof (i,o))
-- try1Proof i (f:fx) = proofify f i <|> try1Proof i fx

-- proofify :: [i -> R o] -> i -> R (Proof (i,o))
-- proofify rs i = do
--   o <- try i rs
--   return $ Proof (i,o) []


{-
rule i@(i1 i2) = do 
  [o1,o2] <- tries i [rule]
-}