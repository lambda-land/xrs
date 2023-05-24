{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Lang.Classification where



import Logic.Proof ( Proof )
import Data.Proxy (Proxy)

class Context c j where
  -- Initial context for the root judgement
  rootCtx :: Proxy j -> c
  -- Compute the child contexts for a node in the proof tree
  childContexts :: c -> Proof j -> [c]


class Context c j => Classification h j c | h -> j c where
  -- Compute the heuristic value for every node in the proof tree based on a context
  classify :: c -> j -> [Proof (h,j)] -> h


data Polarity = Pos | Neg deriving (Show,Eq)

class Score h where
  polarity :: Polarity
  polarity = Pos
  score :: h -> Float


class Classification h j c => Strategy h j c | h -> j c where
  pick :: Proof j -> [j]


