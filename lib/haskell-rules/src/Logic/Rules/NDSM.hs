{-#LANGUAGE DeriveFunctor #-}
module Logic.Rules.NDSM where

import Control.Monad
import Data.Data
import Control.Applicative



newtype NDSM s a = NDSM {unNDSM :: (s -> [(s,a)])} deriving (Functor)

instance Monad (NDSM s) where
	return x = NDSM (\s -> [(s,x)])
	(NDSM f) >>= c = NDSM (\s -> let svl = f s
					 ml = map (\(_,x)->(unNDSM $ c x)) svl
					 sl = map fst svl
					 aml = zipWith ($) ml sl
				     in concat aml)


instance MonadPlus (NDSM s) where
	mzero = NDSM (const [])
	mplus (NDSM x) (NDSM y) = NDSM (\s->(x s)++(y s))

instance Applicative (NDSM s) where
    pure = return
    (<*>) = ap

instance Alternative (NDSM s) where
    empty = mzero
    (<|>) = mplus
onState :: (s -> s) -> NDSM s ()
onState f = NDSM (\s->[(f s,())])

fromState :: (s -> a) -> NDSM s a
fromState f = NDSM (\s->[(s, f s)])

runNDSM :: NDSM s a -> s -> [(s,a)]
runNDSM (NDSM f) = f
