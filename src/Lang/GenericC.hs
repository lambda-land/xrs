{-# LANGUAGE OverloadedStrings, DeriveGeneric, DefaultSignatures,MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances #-}


module Lang.GenericC where

import Data.Data
import Data.Typeable
import GHC.Generics
import Data.Proxy


-- >>> 3 + 4
-- 7

{-

data Proof j = Node j [Proof j]




class GContext f j where
  gRootCtx :: f c -> (Proxy j) -> f c
  gChildContexts :: f c -> Proof j -> [f c]


instance GContext U1 j where
  gRootCtx U1 _ = U1
  gChildContexts U1 _ = U1

instance (GContext a j,GContext b j) => GContext (a :*: b) j where
  gRootCtx (a :*: b) p = (gRootCtx a p) :*: (gRootCtx b p)
  gChildContexts (a :*: b) p = zipWith (:*:) (gChildContexts a p) (gChildContexts b p)
 
instance (Context c j, Typeable c) => GContext (K1 i c) j where
  gRootCtx k _ = k
  gChildContexts (K1 c) proof = K1 <$> childContexts c proof

instance (GContext a j) => GContext (M1 i c a) j where
  gRootCtx m p = M1 (gRootCtx (unM1 m) p)
  gChildContexts (M1 a) proof = M1 <$> gChildContexts a proof

instance (GContext a j, GContext b j) => GContext (a :+: b) j where
  gRootCtx (L1 a) p = L1 (gRootCtx a p)
  gRootCtx (R1 b) p = R1 (gRootCtx b p)
  gChildContexts (L1 a) proof = L1 <$> gChildContexts a proof
  gChildContexts (R1 b) proof = R1 <$> gChildContexts b proof

class Context c j where
  rootCtx :: Proxy j -> c
  childContexts :: c -> Proof j -> [c]
  
  default rootCtx :: (Generic c, GContext (Rep c) j) => Proxy j -> c
  rootCtx p = to $ gRootCtx (from $ rootCtx p) p


-}
--
--class GContext f j where
--  gRootCtx :: Proxy j -> f p
--  gChildContexts :: f p -> Proof j -> [f p]
--
--instance (Context c j) => GContext (K1 i c) j where
--  gRootCtx _ = K1 $ rootCtx (Proxy :: Proxy j)
--  gChildContexts (K1 c) proof = K1 <$> childContexts c proof
--
--instance (GContext a j, GContext b j) => GContext (a :*: b) j where
--  gRootCtx _ = gRootCtx (Proxy :: Proxy j) :*: gRootCtx (Proxy :: Proxy j)
--  gChildContexts (a :*: b) proof = (++) <$> gChildContexts a proof <*> gChildContexts b proof
--
--instance (GContext a j) => GContext (M1 i c a) j where
--  gRootCtx _ = M1 $ gRootCtx (Proxy :: Proxy j)
--  gChildContexts (M1 a) proof = M1 <$> gChildContexts a proof
--
--class (Generic a, GContext (Rep a) j) => Context a j where
--  genericRootCtx :: Proxy j -> a
--  genericRootCtx _ = to $ gRootCtx (Proxy :: Proxy j)
--
--  genericChildContexts :: a -> Proof j -> [a]
--  genericChildContexts a proof = to <$> gChildContexts (from a) proof
--  
--
--  rootCtx :: Proxy j -> c
--  childContexts :: c -> Proof j -> [c]
--
--  default rootCtx :: (Context a j) => Proxy j -> a
--  rootCtx = genericRootCtx
--
--  default childContexts :: (Context a j) => a -> Proof j -> [a]
--  childContexts = genericChildContexts
--  
--
----class Context c j where
----  rootCtx :: Proxy j -> c
----  childContexts :: c -> Proof j -> [c]
--
main = print "Hello"
--
