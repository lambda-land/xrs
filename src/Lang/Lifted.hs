{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
module Lang.Lifted where


import Logic.Proof
import Lang.Lang
import Lang.Operation

import Data.List (intercalate)


data LiftedEvalJ
  = LiftedEvalJ { given :: EvalJ
                , results :: [EvalJ]
                } deriving Eq

instance Show LiftedEvalJ where
  show (LiftedEvalJ j js) = "<" ++ show j ++ " | " ++ intercalate "," (map show js) ++ ">"



pattern (:=>) e v <- EvalJ _ _ e v

pattern (:|-) ts j = Proof j ts

-- pattern Val <- (isValue -> True)

getValue :: Expr -> [Proof EvalJ] -> Val
getValue e ts = (\(EvalJ _ _ _ v) -> v) $ head $ filter (\(EvalJ _ _ e' _) -> e == e') (map conclusion ts)
  where js = map conclusion ts

getResults :: EvalJ -> [Proof LiftedEvalJ] -> [EvalJ]
getResults j ts = results $ head $ filter (\(LiftedEvalJ j' _) -> j == j') (map conclusion ts)

lift :: Proof EvalJ -> Proof LiftedEvalJ
lift (Proof j@(EvalJ d rho e v) ts)
  = let partialJ = EvalJ d rho
        (.=>) = partialJ
        ts' = map lift ts
        liftedJ = LiftedEvalJ j
      in case j of
      (Val :=> _)    -> ts' :|- liftedJ [j]
      (EVar _ :=> _) -> ts' :|- liftedJ [j]
      (EOp e1 op e2 :=> v) ->
          let v1 = getValue e1 ts
              v2 = getValue e2 ts
              in ts' :|- liftedJ [EOp (embed v1) op (embed v2) .=> v]
      (EApp e1 e2 :=> v) ->
          let v1 = getValue e1 ts
              v2 = getValue e2 ts
              x1 = getResults (e1 .=> v1) ts'
              x2 = getResults (e2 .=> v2) ts'
              in ts' :|- liftedJ ([e1 .=> v1,EApp (embed v1) (embed v2) .=> v] ++ x1 ++ x2)


-- lift (Proof (EInt _ :=>: _) ps) = 


-- class Lifted j1 j2 where
--   lift :: Proof j1 -> Proof j2

-- instance Lifted EvalJ LiftedEvalJ where
--   lift :: Proof EvalJ -> Proof LiftedEvalJ
--   lift = undefind 


