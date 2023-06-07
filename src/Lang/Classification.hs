{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Lang.Classification where



import Logic.Proof
import Data.Proxy
import Data.List (sortOn)

class Context ctx judge where
  -- Initial context for the root judgement
  rootCtx :: Proxy judge -> ctx
  -- Compute the child contexts for a node in the proof tree
  childContexts :: ctx -> Proof judge -> [ctx]


class Context ctx judge => Classification c judge ctx | c -> judge ctx where
  -- Compute the heuristic value for every node in the proof tree based on a context
  classify :: ctx -> judge -> [Proof (c,judge)] -> c


data Polarity = Pos | Neg deriving (Show,Eq)


class Score c where
  polarity :: Polarity
  polarity = Pos
  score :: c -> Float



class Classification c judge ctx => Strategy c judge ctx | c -> judge ctx where
  pick :: Proof (c,judge) -> [judge]

pick' :: forall c judge ctx. Strategy c judge ctx => Proof judge -> [judge]
pick' x = pick $ annotate @c @judge @ctx x

-- pick' =       annotate @c @judge @ctx   >=> select @c @judge @ctx
--    = \x -> annotate @c @judge @ctx x >>= select @c @judge @ctx



annotate :: forall c judge ctx. Classification c judge ctx => Proof judge -> Proof (c,judge)
annotate = annotate' (rootCtx @ctx @judge Proxy)
  where annotate' ctx n@(Node j ps) = Node (h, j) ps' where
          ctxs' = childContexts ctx n
          ps' = zipWith annotate' ctxs' ps
          h = classify ctx j ps'




selectByAnnotation :: (c -> Bool) -> Proof (c,judge) -> [judge]
selectByAnnotation f = map snd . filter (f . fst) . toList'




{-  This is very specific to classifications that you can score -}

selectCustom' :: forall c judge ctx a. (Ord a, Classification c judge ctx) => (c -> a) -> Proof judge -> [(c,judge)]
selectCustom' score = reverse . sortOn (score . fst) . toList' . annotate @c


selectCustom :: forall c judge ctx a. (Ord a, Classification c judge ctx) => (c -> a) -> Proof judge -> [judge]
selectCustom score = map snd . selectCustom' score


measure :: forall c. Score c => c -> Float
measure h | polarity @c == Pos = score h
          | polarity @c == Neg = 1.0 - score h

select :: forall c judge ctx. (Classification c judge ctx, Score c) => Proof judge -> [judge]
select = selectCustom (measure @c)

-- we are not providing this instance, since it could overlap with manual Strategy instances:
-- instance (Classification c judge ctx, Score c) => Strategy c judge ctx where
--   pick = select @c

-- if you want this functionality, you can write it manually, like:
-- instance Strategy MyC EvalJ MyCtx where
--   pick = select @MyC






