module Lang.Parser where

import Lang.ParParser   ( pSCPL, myLexer )
import Lang.ASTConverter ( transSCPL )
import Lang.LayoutParser ( resolveLayout )

import Lang.Lang
import Lang.Operation

import Data.Maybe (fromJust)


parseFromFile :: FilePath -> IO (Either String [(String,Expr)])
parseFromFile f = do
  s <- readFile f
  return (parse s)


getRight :: Either String b -> b
getRight (Left x)  = error x
getRight (Right x) = x

getBinding :: String -> Either String [(String,Expr)] -> Expr
getBinding s = fromJust . lookup s . getRight

-- getExampleFromFile :: FilePath -> String -> IO Expr
-- getExampleFromFile f s = do
--   p <- parseFromFile f
--   return (getBinding s p)
-- getExampleFromFile' = getExampleFromFile "app/Ex1.xr"
-- getExampleFromFile'' = pullOutIO . getExampleFromFile "app/Ex1.xr"
-- evalFromFile en = getExampleFromFile "app/Ex1.xr" en >>= (\e -> print $ eval [] e)

-- traceFromFile en = getExampleFromFile "app/Ex1.xr" en >>= (\e -> print $ trace e)
-- traceProblemsFromFile en = getExampleFromFile "app/Ex1.xr" en >>= (\e -> print $ traceProblems e)


-- traceFromFile' en = getExampleFromFile "app/Ex1.xr" en >>= (\e -> return $ trace e)

-- traceFromFileTill n en = getExampleFromFile "app/Ex1.xr" en >>= (\e -> print $  hidePast n $ trace e)


parse :: String -> Either String [(String,Expr)]
parse s = case pSCPL (resolveLayout False $ myLexer s) of 
            Left err -> Left err
            Right x  -> Right (transSCPL x)

parseString :: String -> Expr
parseString s = getBinding "expr" (parse $ "expr = " ++ s)
