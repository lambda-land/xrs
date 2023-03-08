module Lang.Parser where

import Lang.ParParser   ( pSCPL, myLexer )
import Lang.ASTConverter ( transSCPL )
import Lang.LayoutParser ( resolveLayout )

import Lang.Lang
import Lang.Operation

import Data.Maybe (fromJust)
import Tools (coio)

type ParseError = String
type ParseResult = Either ParseError GlobalEnv -- Either String [(String,Expr)]

parseFromFile :: FilePath -> IO ParseResult
parseFromFile f = do
  s <- readFile f
  return (parse s)


getRight :: Either String b -> b
getRight (Left x)  = error x
getRight (Right x) = x

getBinding :: String -> ParseResult -> Expr
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

-- reallyStupidFixPrashantPleaseHelp :: String -> Either String [(String,Expr)]

reallyStupidFixPrashantPleaseHelp :: String -> ParseResult
reallyStupidFixPrashantPleaseHelp s = consolidate results
  where ss = filter (not . null) $ coagulate [[]] (lines s)
        coagulate xss [] = xss
        coagulate xss ([]:xs) = coagulate ([]:xss) xs
        coagulate (xs:xss) (x:xs') = coagulate ((xs ++ "\n" ++ x):xss) xs'
        results = map parse ss
        consolidate ((Left x):_) = Left x
        consolidate ((Right x):xs) = consolidate xs >>= Right . (x++)
        consolidate [] = Right []

parse :: String -> ParseResult
parse s = case pSCPL (resolveLayout False $ myLexer s) of 
            Left err -> Left err
            Right x  -> Right (transSCPL x)

parseProgram :: String -> GlobalEnv
parseProgram s = case reallyStupidFixPrashantPleaseHelp s of
                   Left err -> error err
                   Right x  -> x

parseString :: String -> Expr
parseString s = getBinding "expr" (parse $ "expr = " ++ s)


loadFile :: String -> GlobalEnv
loadFile = parseProgram . coio .readFile



