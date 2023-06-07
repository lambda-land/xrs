{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}



module Lang.ClassificationInstances where


import Lang.Classification


import Data.Data (Proxy (Proxy))
import Data.List (sortOn)
import Logic.Proof
import Lang.Operation
import Lang.Lang
import GHC.Base (neChar)
import Data.Bifunctor (first,bimap)

import Lang.Evaluation (traceExample)
import Lang.Denotation (runArithmetic,isBuiltIn, runBinOp)


{-
class Context c j where
  -- Initial context for the root judgement
  rootCtx :: Proxy j -> c
  -- Compute the child contexts for a node in the proof tree
  childContexts :: c -> Proof j -> [c]
-}

-- data MH = MH { c1 :: IsBaseCase, c2 :: IsArith, c3 :: IsLiteral } deriving Show
-- derivingClassify ''MH


instance Context () j where
  rootCtx _ = ()
  childContexts _ (Node _ ps) = [() | _ <- ps]

instance (Context a j, Context b j) => Context (a,b) j where
  rootCtx p = (rootCtx p, rootCtx p)
  childContexts (a, b) n = zip (childContexts a n) (childContexts b n)

instance (Context (a,b) j, Context c j) => Context (a,b,c) j where
  rootCtx p = let (c1,c2) = rootCtx p in (c1,c2,rootCtx p)
  childContexts (a,b, c) n = zipWith (\(a',b') c' -> (a',b',c')) (childContexts (a,b) n) (childContexts c n)






{-
class Context c j => Classify h j c | h -> j c where
  -- Compute the heuristic value for every node in the proof tree based on a context
  classify :: c -> j -> [Proof (h,j)] -> h
-}
  -- h is the type of the classificiation data
  -- j is the type of the judgement
  -- c is the type of the context

unzipProof :: Proof ((h1, h2), j) -> (Proof (h1, j), Proof (h2, j))
unzipProof ps = (fmap (first fst) ps, fmap (first snd) ps)

instance (Classification h1 j c1, Classification h2 j c2) => Classification (h1,h2) j (c1,c2) where
  classify (c1,c2) j ps = (classify c1 j ps1, classify c2 j ps2) where
    (ps1, ps2) = unzip $ map unzipProof ps



{-
data Polarity = Pos | Neg deriving (Show,Eq)

class Score h where
  polarity :: Polarity
  polarity = Pos
  score :: h -> Float
-}






newtype IsArith = IsArith Bool deriving (Show)

instance Classification IsArith EvalJ () where
  classify _ (EvalJ _ _ (EOp {}) _) _ = IsArith True
  classify _ _ _ = IsArith False

isArithScore (IsArith True) = 1.0
isArithScore (IsArith False) = 0.0

instance Score IsArith where
  polarity = Neg
  score = isArithScore









newtype IsLiteral = IsLiteral Bool deriving (Show)

instance Classification IsLiteral EvalJ () where
  classify _ (EvalJ _ _ e _) _ = IsLiteral (isLiteral e)
    where isLiteral (EInt _) = True
          isLiteral (EBool _) = True
          isLiteral (EStr _) = True
          isLiteral (EChar _) = True
          isLiteral (EVar _) = True
          isLiteral (EList xs) = all isLiteral xs
          isLiteral _ = False

isLiteralScore (IsLiteral True) = 1.0
isLiteralScore (IsLiteral False) = 0.0

instance Score IsLiteral where
  polarity = Neg
  score = isLiteralScore







newtype IsConditional = IsConditional Bool deriving Show

newtype IsConditionalCTX = IsConditionalCTX Bool

instance Context IsConditionalCTX EvalJ where
  rootCtx _ = IsConditionalCTX False
  childContexts (IsConditionalCTX b) (Node (EvalJ _ _ (EIf _ _ _) _) _)
    = [IsConditionalCTX True, IsConditionalCTX b]
  childContexts (IsConditionalCTX b) (Node _ ps) = IsConditionalCTX b <$ ps

instance Classification IsConditional EvalJ IsConditionalCTX where
  classify (IsConditionalCTX b) _ _ = IsConditional b

isConditionalScore (IsConditional True) = 1.0
isConditionalScore (IsConditional False) = 0.0

instance Score IsConditional where
  polarity = Neg
  score = isConditionalScore









-- doesn't work for functions like
-- fac = fun n -> if n == 0 then 1 else n * (id fac) (n-1)
doesOccurAgain :: Var -> Proof EvalJ -> Bool
doesOccurAgain n (Node (EvalJ _ _ (EApp (EVar n') _) _) ps) | n == n' = True
doesOccurAgain n (Node _ ps) = any (doesOccurAgain n) ps

newtype IsBaseCase = BHC Bool 

instance Show IsBaseCase where
  show (BHC b) = if b then "base case" else "not base case"

instance Classification IsBaseCase EvalJ () where
  classify () j@(EvalJ _ _ (EApp (EVar n) _) _) ps
    | isBuiltIn n = BHC False
    | doesOccurAgain n (fmap snd (ps !! 2)) = BHC False
    -- builtin functions fail this test
    | length ps < 3 = error (show (j, map conclusion (fmap (fmap snd) ps)))
    | otherwise = BHC True
  classify _ _ _ = BHC False

baseCaseScore :: IsBaseCase -> Float
baseCaseScore (BHC True) = 1.0
baseCaseScore (BHC False) = 0.0

instance Score IsBaseCase where
  polarity = Pos
  score = baseCaseScore







newtype IsBinOp = IsBinOp Bool deriving Show

instance Classification IsBinOp EvalJ () where
  classify _ (EvalJ _ _ e@(EOp _ _ _) _) _ | containsApp e = IsBinOp True
  classify _ _ _ = IsBinOp False

binOpScore :: IsBinOp -> Float
binOpScore (IsBinOp True) = 1.0
binOpScore (IsBinOp False) = 0.0

instance Score IsBinOp where
  polarity = Pos
  score = binOpScore



newtype IsIfExpr = IsIfExpr Bool deriving Show

instance Classification IsIfExpr EvalJ () where
  classify _ (EvalJ _ _ (EIf _ _ _) _) _ = IsIfExpr True
  classify _ _ _ = IsIfExpr False

ifExprScore :: IsIfExpr -> Float
ifExprScore (IsIfExpr True) = 1.0
ifExprScore (IsIfExpr False) = 0.0

instance Score IsIfExpr where
  polarity = Neg
  score = ifExprScore




-- Increases with the number of recursive calls
newtype IsRelevantRecCall = IsRelevantRecCall Int deriving Show

newtype IsRelevantRecCallCTX = IsRelevantRecCallCTX Int

instance Context IsRelevantRecCallCTX EvalJ where
  rootCtx _ = IsRelevantRecCallCTX 0
  childContexts (IsRelevantRecCallCTX n) (Node (EvalJ _ _ (EApp _ _) _) ps) = map IsRelevantRecCallCTX [n,n,n+1] 
  childContexts (IsRelevantRecCallCTX n) (Node _ ps) = IsRelevantRecCallCTX n <$ ps

instance Classification IsRelevantRecCall EvalJ IsRelevantRecCallCTX where
  -- classify (IsRelevantRecCallCTX n) (EvalJ _ _ (EApp _ _) _) _ = IsRelevantRecCall n
  classify (IsRelevantRecCallCTX n) _ _ = IsRelevantRecCall n


relevantRecCallScore :: IsRelevantRecCall -> Float
relevantRecCallScore (IsRelevantRecCall n) = 1.0 / (fromIntegral n + 1.0)

instance Score IsRelevantRecCall where
  score = relevantRecCallScore




newtype IsClosure = IsClosure Bool deriving Show

instance Context IsClosure EvalJ where
  rootCtx _ = IsClosure False
  childContexts b (Node _ ps) = b <$ ps

instance Classification IsClosure EvalJ () where
  classify _ (EvalJ _ _ _ (VClosure {})) _ = IsClosure True
  classify _ _ _ = IsClosure False

closureScore :: IsClosure -> Float
closureScore (IsClosure True) = 1.0
closureScore (IsClosure False) = 0.0

instance Score IsClosure where
  polarity = Neg
  score = closureScore

type CustomClassify = (((((((IsArith, IsLiteral), IsConditional), IsBaseCase), IsClosure),IsBinOp),IsIfExpr),IsRelevantRecCall)

-- data CustomClassify = CC { isArith :: IsArith
--                          , isLiteral :: IsLiteral
--                          , isConditional :: IsConditional
--                          , isBaseCase :: IsBaseCase
--                          , isClosure :: IsClosure
--                          , isBinOp :: IsBinOp
--                          , isIfExpr :: IsIfExpr
--                          , isRelevantRecCall :: IsRelevantRecCall
--                          } 

-- deriveClassify ''CustomClassify

weightedCustomScore :: CustomClassify -> Float
weightedCustomScore (((((((ia, it), ic), ibc),icl),ibo),iif),irrc) =
  -- dot (
  --   0.14,  -- IsArith
  --   0.15,  -- IsLiteral
  --   0.14,  -- IsConditional
  --   0.15,  -- IsBaseCase
  --   0.14,  -- IsClosure
  --   0.14,  -- IsBinOp
  --   0.14,  -- IsIfExpr
  --   0.14   -- IsRelevantRecCall
  -- )
  0.14 * measure ia +
  0.15 * measure it +
  0.14 * measure ic +
  0.15 * measure ibc + 
  0.14 * measure icl + 
  0.14 * measure ibo + 
  0.14 * measure iif +
  0.14 * measure irrc



-- data CustomClassifyT 
--   = CustomIsArith Bool
--   | CustomIsLiteral Bool
--   | CustomIsConditional Bool
--   | CustomIsBaseCase Bool
--   | CustomIsClosure Bool
--   | CustomIsBinOp Bool
--   | CustomIsIfExpr Bool
--   | CustomIsRelevantRecCall Bool

-- instance CustomClassify'

-- type CustomClassify' = [(CustomClassifyT,Float)]



-- in theory, it should be possible to get an instance like:
-- Classify CustomClassifyNT EvalJ (((), IsConditionalCTX), ())
-- because we also have
-- Classify CustomClassify EvalJ (((), IsConditionalCTX), ())
-- and this is just a newtype around CustomClassify.
newtype CustomClassifyNT = CustomClassifyNT CustomClassify




runExample :: String -> IO ()
runExample es = do
  let hjs = selectCustom' weightedCustomScore $ traceExample es
  let hjs' = map (bimap id fillEnvJ) hjs
  putStrLn "\n--- Unchanged Judgments ---\n"
  mapM_ (putStrLn . ("    "++) . show) $ take 1000 $ map snd $ hjs
  let hjs'' = map (bimap id postProcessJ) hjs'
  putStrLn "\n--- Post Processed ---\n"
  mapM_ (putStrLn . ("    "++) . show) $ take 1000 $ map snd $ hjs''
  -- mapM_ (putStrLn . ("    "++) . postProcess . ArithmeticPostProcess ) $ take 10 $ map snd $ hjs
  -- mapM_ (putStrLn . ("    "++) . postProcess . SimpleArithmeticPostProcess ) $ take 10 $ map snd $ hjs



postProcessJ :: EvalJ -> EvalJ
postProcessJ = exprMap runArithmetic . fillEnvJ

class PostProcessing a where
  postProcess :: a -> String

newtype CanonicalPostProcess j = CanonicalPostProcess j

instance Show j => PostProcessing (CanonicalPostProcess j) where
  postProcess (CanonicalPostProcess j) = show j


newtype ArithmeticPostProcess = ArithmeticPostProcess EvalJ

instance PostProcessing ArithmeticPostProcess where
  postProcess (ArithmeticPostProcess j) = show . exprMap runArithmetic . fillEnvJ $ j


newtype SimpleArithmeticPostProcess = SimpleArithmeticPostProcess EvalJ

instance PostProcessing SimpleArithmeticPostProcess where
  postProcess (SimpleArithmeticPostProcess j) = show . exprMap runArithmeticSimple . fillEnvJ $ j
    where runArithmeticSimple :: Expr -> Expr
          runArithmeticSimple e = case e of
            EOp e1 op e2 -> case (runArithmeticSimple e1, runArithmeticSimple e2) of
                              (EInt a, EInt b) | op `elem` [Add,Sub] -> embed (runBinOp op (VInt a) (VInt b))
                              (a, b) -> EOp a op b
            EIf e1 e2 e3 -> EIf (runArithmeticSimple e1) (runArithmeticSimple e2) (runArithmeticSimple e3)
            EApp e1 e2   -> EApp (runArithmeticSimple e1) (runArithmeticSimple e2)
            ELet v e1 e2 -> ELet v (runArithmeticSimple e1) (runArithmeticSimple e2)
            ELam v e'    -> ELam v (runArithmeticSimple e')
            EList es     -> EList (map runArithmeticSimple es)
            _            -> e

-- instance (Context a j, Context b j, Context c j) => Context (a,b,c) j where
--   rootCtx p = (rootCtx p, rootCtx p, rootCtx p)
--   childContexts (a,b,c) n = zip3 (childContexts a n) (childContexts b n) (childContexts c n)

-- instance (Classify h1 j c1, Classify h2 j c2, Classify h3 j c3) => Classify (h1,h2,h3) j (c1,c2,c3) where


instance (Context (a,b,c) j, Context d j) => Context (a,b,c,d) j where
  rootCtx p = let (c1,c2,c3) = rootCtx p in (c1,c2,c3,rootCtx p)
  childContexts (a,b, c,d) n = zipWith (\(a',b',c') d' -> (a',b',c',d')) (childContexts (a,b,c) n) (childContexts d n)


instance (Context (a,b,c,d) j, Context e j) => Context (a,b,c,d,e) j where
  rootCtx p = let (c1,c2,c3,c4) = rootCtx p in (c1,c2,c3,c4,rootCtx p)
  childContexts (a,b, c,d,e) n = zipWith (\(a',b',c',d') e' -> (a',b',c',d',e')) (childContexts (a,b,c,d) n) (childContexts e n)

instance (Context (a,b,c,d,e) j, Context f j) => Context (a,b,c,d,e,f) j where
  rootCtx p = let (c1,c2,c3,c4,c5) = rootCtx p in (c1,c2,c3,c4,c5,rootCtx p)
  childContexts (a,b, c,d,e,f) n = zipWith (\(a',b',c',d',e') f' -> (a',b',c',d',e',f')) (childContexts (a,b,c,d,e) n) (childContexts f n)


instance (Context (a,b,c,d,e,f) j, Context g j) => Context (a,b,c,d,e,f,g) j where
  rootCtx p = let (c1,c2,c3,c4,c5,c6) = rootCtx p in (c1,c2,c3,c4,c5,c6,rootCtx p)
  childContexts (a,b, c,d,e,f,g) n = zipWith (\(a',b',c',d',e',f') g' -> (a',b',c',d',e',f',g')) (childContexts (a,b,c,d,e,f) n) (childContexts g n)


instance (Context (a,b,c,d,e,f,g) j, Context h j) => Context (a,b,c,d,e,f,g,h) j where
  rootCtx p = let (c1,c2,c3,c4,c5,c6,c7) = rootCtx p in (c1,c2,c3,c4,c5,c6,c7,rootCtx p)
  childContexts (a,b, c,d,e,f,g,h) n = zipWith (\(a',b',c',d',e',f',g') h' -> (a',b',c',d',e',f',g',h')) (childContexts (a,b,c,d,e,f,g) n) (childContexts h n)


instance (Context (a,b,c,d,e,f,g,h) j, Context i j) => Context (a,b,c,d,e,f,g,h,i) j where
  rootCtx p = let (c1,c2,c3,c4,c5,c6,c7,c8) = rootCtx p in (c1,c2,c3,c4,c5,c6,c7,c8,rootCtx p)
  childContexts (a,b, c,d,e,f,g,h,i) n = zipWith (\(a',b',c',d',e',f',g',h') i' -> (a',b',c',d',e',f',g',h',i')) (childContexts (a,b,c,d,e,f,g,h) n) (childContexts i n)

instance (Context (a,b,c,d,e,f,g,h,i) j, Context j' j) => Context (a,b,c,d,e,f,g,h,i,j') j where
  rootCtx p = let (c1,c2,c3,c4,c5,c6,c7,c8,c9) = rootCtx p in (c1,c2,c3,c4,c5,c6,c7,c8,c9,rootCtx p)
  childContexts (a,b, c,d,e,f,g,h,i,j) n = zipWith (\(a',b',c',d',e',f',g',h',i') j' -> (a',b',c',d',e',f',g',h',i',j')) (childContexts (a,b,c,d,e,f,g,h,i) n) (childContexts j n)

instance (Context (a,b,c,d,e,f,g,h,i,j') j, Context k j) => Context (a,b,c,d,e,f,g,h,i,j',k) j where
  rootCtx p = let (c1,c2,c3,c4,c5,c6,c7,c8,c9,c10) = rootCtx p in (c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,rootCtx p)
  childContexts (a,b, c,d,e,f,g,h,i,j,k) n = zipWith (\(a',b',c',d',e',f',g',h',i',j') k' -> (a',b',c',d',e',f',g',h',i',j',k')) (childContexts (a,b,c,d,e,f,g,h,i,j) n) (childContexts k n)


instance (Context (a,b,c,d,e,f,g,h,i,j',k) j, Context l j) => Context (a,b,c,d,e,f,g,h,i,j',k,l) j where
  rootCtx p = let (c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11) = rootCtx p in (c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,rootCtx p)
  childContexts (a,b, c,d,e,f,g,h,i,j,k,l) n = zipWith (\(a',b',c',d',e',f',g',h',i',j',k') l' -> (a',b',c',d',e',f',g',h',i',j',k',l')) (childContexts (a,b,c,d,e,f,g,h,i,j,k) n) (childContexts l n)


-- instance (Classify h1 j c1, Classify h2 j c2) => Classify (h1,h2) j (c1,c2) where
--   classify (c1,c2) j ps = (classify c1 j ps1, classify c2 j ps2) where
--     (ps1, ps2) = unzip $ map unzipProof ps

thd :: (a,b,c) -> c
thd (_,_,c) = c

fth :: (a,b,c,d) -> d
fth (_,_,_,d) = d


-- unzipProof3 :: Proof ((h1, h2, h3), j) -> (Proof (h1, j), Proof (h2, j), Proof (h3, j))
-- unzipProof3 ps = (fmap (first fst) ps, fmap (first snd) ps, )

-- instance (Classify (h1,h2) j (c1,c2), Classify h3 j c3) => Classify (h1,h2,h3) j (c1,c2,c3) where
--   classify (c1,c2,c3) j ps = (classify c1 j ps1, classify c2 j ps2, classify c3 j ps3)
--     where (ps1, ps2, ps3) = unzip3 $ map unzipProof ps
          




{- chris newfile  
class Generic a => GenericClassify a where
  type Context = -- written through ghc generics
  -- this has a function which has a default impl written using ghc generics
  genericClassify :: ...

instance GenericClassify h => Classify h j (Context h) where
  classify = genericClassify

data MyCustomClassify = MyCustomClassify IsArith IsLiteral IsConditional IsBaseCase IsClosure IsBinOp IsIfExpr IsRelevantRecCall
  deriving (Generic, GenericClassify)

instance Score MyCustomClassify where
  score = genericScore (0.14, 0.15, 0.14, 0.15, 0.14, 0.14, 0.14, 0.14)
-}




type TestClassification = (IsBaseCase,IsRelevantRecCall)


instance Strategy TestClassification EvalJ ((),IsRelevantRecCallCTX) where
  pick :: Proof (TestClassification,EvalJ) -> [EvalJ]
  pick pf = selectByAnnotation selection pf
    where -- pf' = annotate @TestClassification pf
          selection (BHC True,_) = True
          selection (_,IsRelevantRecCall 1) = True
          selection (_,_) = False


pickTestClassficationStrategy = pick' @TestClassification -- $ traceExample "fac 5"
