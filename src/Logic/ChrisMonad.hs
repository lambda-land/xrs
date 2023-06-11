module Logic.ChrisMonad where

import Control.Monad (ap)


{-
data RoseTree a = Node a [RoseTree a] deriving (Show)
data NState s a = NState a [RoseTree s] deriving (Functor)

instance Applicative (NState s) where
  pure a = NState a []
  (<*>) = ap


instance Monad (NState s) where
  return = pure
  (>>=) = bind

run      :: NState a a -> RoseTree a
addChild :: NState s s -> NState s s
bind     :: NState s a -> (a -> NState s b) -> NState s b

run (NState a ps) = Node a ps
addChild (NState a ps) = NState a [Node a ps]
bind (NState a ps) f = let NState b ps' = f a in NState b (ps <> ps')

main :: IO ()
main = print $ run $ do
  x <- addChild (return 1)
  y <- addChild (return 2)
  return (x + y)

-}