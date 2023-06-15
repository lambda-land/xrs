module Control.Monad.Trace where
-- import Control.Monad.Trans.Class
-- import Control.Monad.Trans.State
-- import Control.Monad.Identity

-- data Tree a = Node a [Tree a] deriving (Show)

-- newtype TraceT s m a = TraceT { runTraceT :: StateT s m (a, Tree (s, s)) }

-- instance Functor m => Functor (TraceT s m) where
--   fmap f (TraceT sma) = TraceT $ fmap (first f) sma
--     where
--       first f (a, t) = (f a, t)

-- instance Applicative m => Applicative (TraceT s m) where
--   pure x = TraceT $ pure (x, Node (undefined, undefined) [])
--   (TraceT smf) <*> (TraceT sma) = TraceT $ (\(f, tf) (a, ta) -> (f a, Node (undefined, undefined) [tf, ta])) <$> smf <*> sma

-- instance Monad m => Monad (TraceT s m) where
--   (TraceT sma) >>= f = TraceT $ do
--     (a, ta) <- sma
--     s <- get
--     let (TraceT smb) = f a
--     (b, tb) <- smb
--     return (b, Node (s, snd $ head $ children tb) [ta, tb])
--     where
--       children (Node _ cs) = cs

-- instance MonadTrans (TraceT s) where
--   lift ma = TraceT $ lift ma >>= \a -> return (a, Node (undefined, undefined) [])

-- runTrace :: (Monad m) => s -> TraceT s m a -> m (Tree (s, s))
-- runTrace s m = snd <$> evalStateT (runTraceT m) s

-- example :: TraceT Int Identity Int
-- example = do
--   x <- TraceT $ return (1, Node (0, 1) [])
--   y <- TraceT $ return (2, Node (1, 2) [])
--   return (x + y)

-- main = print $ runIdentity $ runTrace 0 example

{-
data Tree a = Node a [Tree a] | Leaf deriving Functor

instance Show a => Show (Tree a) where
  show Leaf = "Leaf"
  show (Node a as) = "Node " ++ show a ++ " " ++ show as

root :: Tree a -> a
root (Node a _) = a

fmapM :: (a -> Tree b) -> Tree a -> Tree b
fmapM f Leaf = Leaf
fmapM f (Node a as) = case f a of
  Leaf -> Leaf
  Node b bs -> Node b (map (fmapM f) as)

fmapM' :: (a -> Tree b) -> Tree a -> Tree b
fmapM' f t = unNest $ fmap f t
  where unNest Leaf = Leaf
        unNest (Node Leaf _) = Leaf
        unNest (Node (Node a _) bs) = Node a (map unNest bs)

instance Applicative Tree where
  pure a = Node a []
  Leaf <*> _ = Leaf
  _ <*> Leaf = Leaf
  (Node f fs) <*> t@(Node a as) = Node (f a) (map (fmap f) as ++ map (<*> t) fs)


instance Monad Tree where
  Leaf >>= _ = Leaf
  -- t >>= f = fmapM f t
  Node a as >>= f = case f a of
    Leaf -> Leaf
    -- Node b bs -> Node b $ (fmapM f (Node a as) : bs)
    Node b bs -> Node b (bs ++ map (>>= f) as)


-- yield :: a -> Tree a


addChild :: Tree a -> Tree a
addChild Leaf = Leaf
addChild (Node a as) = Node a (Leaf : as)

seqTree :: (a -> Tree a) -> [Tree a] -> a -> Tree a
seqTree f ts a = case f a of
  Leaf -> Node a ts
  Node b bs -> Node b (bs ++ ts)

test :: Tree Int
test = do
  x <- return 1
  y <- return 2
  return (x + y)


-- test2 :: Tree Int
-- test2 :: Tree (Int, Int)
test2 = let x = return 1
            y = return 2
            in do
              x' <- x
              y' <- y
              seqTree (\a -> return $ x' + a) [] y'




data State s a = State { runState :: (s -> (a,s))
                       , runTraces :: [s -> Tree (s,a)]
                       }

state :: (s -> (a,s)) -> State s a
state f = State f [\s -> Node (swap $ f s) []]
  where swap (a,b) = (b,a)


-- runState :: State s a -> (s -> (a,s))
-- runState (State f) = f

instance Functor (State s) where
  fmap f (State g ts) = State ((\(a,s) -> (f a,s)) . g) (map (\tf -> (\s -> fmap (\(s',a) -> (s',f a)) $ tf s)) ts)

instance Applicative (State s) where
  pure a = State (\s -> (a,s)) [\s -> Node (s,a) []]
  (<*>) s1 s2 = do { f <- s1; a <- s2; return $ f a}

instance Monad (State s) where
  return = pure
  (>>=) (State g ts) f = State run' (map traces' ts)
    where run' s = let (a,s') = g s
                       (State g' _) = f a
                        in g' s'
          traces' tf s = fmap (\(s,a) -> (s,fst $ runState (f a) s)) (tf s)

-- instance Monad (State s) where
--   (>>=) (State g ) f = State $ \s -> let (a,s')     = g s
--                                         (State g') = f a in g' s'

test3 :: State Int Int
test3 = do
  x <- return 1
  y <- return 2
  return (x + y)

-}