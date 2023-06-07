{-#LANGUAGE DeriveFunctor #-}
module Logic.Rules.NDSM where

import Control.Monad
import Data.Data
import Control.Applicative

-- import Control.Monad.State
import Control.Monad.Trans.State


type Branch s a = StateT s [] a

type NDSM s a = Branch s a


onState :: (s -> s) -> NDSM s ()
-- onState :: (s -> s) -> StateT s [] ()
onState f = state (\s -> ((),f s))

fromState :: (s -> a) -> NDSM s a
fromState f = state (\s -> (f s, s))

runNDSM :: NDSM s a -> s -> [(s,a)]
runNDSM st s = map swap $ runStateT st s


mkState :: (s -> [(s,a)]) -> NDSM s a
mkState f = StateT (\s -> map swap $ f s)

swap :: (b, a) -> (a, b)
swap (a,b) = (b,a)


-- newtype NDSM s a = NDSM {unNDSM :: (s -> [(s,a)])} deriving (Functor)


-- instance Monad (NDSM s) where
-- 	return x = NDSM (\s -> [(s,x)])
-- 	(NDSM f) >>= c = NDSM (\s -> let svl = f s
-- 					 ml = map (\(_,x)->(unNDSM $ c x)) svl
-- 					 sl = map fst svl
-- 					 aml = zipWith ($) ml sl
-- 				     in concat aml)


-- instance MonadPlus (NDSM s) where
-- 	mzero = NDSM (const [])
-- 	mplus (NDSM x) (NDSM y) = NDSM (\s->(x s)++(y s))

-- instance Applicative (NDSM s) where
--     pure = return
--     (<*>) = ap

-- instance Alternative (NDSM s) where
--     empty = mzero
--     (<|>) = mplus

