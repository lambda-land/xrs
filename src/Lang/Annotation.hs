

module Lang.Annotations where


import Lang.Lang
import Lang.Denotation
import Lang.Operation
import Logic.Proof


import Lang.Classify

data SimpEvalJ = SimpEvalJ Expr Val
  deriving Eq

instance Show SimpEvalJ where
  show (SimpEvalJ e v) = show e ++ " => " ++ show v



type SimpJList = [SimpEvalJ]


-- instance Classify [SimpEvalJ] () EvalJ where
--   classify :: EvalJ -> () -> [Proof ([SimpEvalJ], ())] -> [SimpEvalJ]
--   classify (EvalJ d rho e v) () _ = undefined



data DepTree a 
  = Single a
  | Sequential [DepTree a]
  | Relaxed [DepTree a]



