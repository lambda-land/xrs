{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, UndecidableInstances #-}
module Logic.Inference where

import Logic.Rules.NDSM
import Logic.Rules.TypeGT
import Logic.Rules.TypeGU

import Logic.Proof



class Judgement i o => Extractable i o j where
  compose :: i -> o -> j
  known :: j -> i

-- instance Extractable i o j => Explain j where
--   premises j = do
--     let i = known j
--     o <- infer i
--     return (compose i o)



-- instance Extractable i o j => Explain (i,o,j) where
--   premises (i,o,j) = infer