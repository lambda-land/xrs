{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}


module Meta.ExperimentTH where

import Control.Applicative
import Language.Haskell.TH
import Control.Monad (unless, replicateM)
import Data.Proxy (Proxy)
import Logic.Proof



{-                  BEGIN CRHIS CODE                 -}

-- a simple type class for demonstration purposes
class A a where
  a :: a



instance A Int where
  a :: Int
  a = 97

instance A Char where 
  a :: Char
  a = 'a'

instance A a => A [a] where 
  a :: A a => [a]
  a = [a]

instance (A a, A b) => A (a, b) where
  a :: (A a, A b) => (a, b)
  a = (a, a)


deriveA :: Name -> Q [Dec]
deriveA ty = do
  info <- reify ty
  dec <- case info of
    TyConI dec -> pure dec
    _ -> fail $ concat ["Type ", show ty, " is not an ADT."]
  constructor <- do
    (ctx, _, ty_params, kind, constructors, _) <-
      case dec of
        DataD ctx name ty_params kind constructors derivings -> pure (ctx, name, ty_params, kind, constructors, derivings)
        NewtypeD ctx name ty_params kind constructor derivings -> pure (ctx, name, ty_params, kind, [constructor], derivings)
        _ -> fail $ concat ["Type ", show ty, " is not `newtype` or `data`."]
    case ctx of [] -> pure ()
                _ -> fail "We don't yet support having any datatype contexts"
    case ty_params of [] -> pure ()
                      _ -> fail "We don't yet support having any type parameters"
    case kind of Nothing -> pure ()
                 _ -> fail "We don't yet support kind annotations"
    case constructors of
      [constructor] -> pure constructor
      _ -> fail "We can only derive for product types, not sum types"
  (conName, paramTypes) <- case constructor of
    NormalC       name fields -> pure (name, [ty | (_, ty) <- fields]) -- ignore strictness/packedness metadata
    RecC          name fields -> pure (name, [ty | (_, _, ty) <- fields]) -- for records we also have field names to ignore
    InfixC field1 name field2 -> pure (name, [ty | (_, ty) <- [field1, field2]])
    _                         -> fail "We don't support any fancy constructors"
  [d|
      instance A $(pure (ConT ty)) where
        a = $(foldl (\f param -> [| $f (a :: $(pure param)) |])
                    (pure (ConE conName))
                    paramTypes)
    |]

{-                  END CRHIS CODE                 -}






-- data Polarity = Pos | Neg deriving (Show,Eq)

class Score a where
  score :: a -> Float
  -- polarity :: Polarity
  -- polarity = Pos

instance Score Float where
  score :: Float -> Float
  score = id

instance Score Int where
  score :: Int -> Float
  score = fromIntegral

instance (Score a, Score b) => Score (a,b) where
  score :: (a,b) -> Float
  score (a,b) = score a + score b



getDec :: Name -> Q Dec
getDec ty = do
  info <- reify ty
  case info of
    TyConI dec -> pure dec
    _ -> fail $ concat ["Type ", show ty, " is not an ADT."]

type DataDecInfo = (Cxt, Name, [TyVarBndr ()], Maybe Kind, [Con], [DerivClause])

getDataDec :: Name -> Q DataDecInfo
getDataDec ty = do
  dec <- getDec ty
  case dec of
    DataD ctx name ty_params kind constructors derivings -> pure (ctx, name, ty_params, kind, constructors, derivings)
    NewtypeD ctx name ty_params kind constructor derivings -> pure (ctx, name, ty_params, kind, [constructor], derivings)
    _ -> fail $ concat ["Type ", show ty, " is not `newtype` or `data`."]

getConstructor :: Name -> Q Con
getConstructor ty = do
  (_, _, ty_params, _, constructors, _) <- getDataDec ty
  unless (null ty_params) $ fail "We don't yet support having any type parameters"
  case constructors of
    [constructor] -> pure constructor
    _ -> fail "We can only derive for product types, not sum types"

getConstructorBody :: Name -> Q (Name,[Type])
getConstructorBody ty = do
  constructor <- getConstructor ty
  case constructor of
    NormalC       name fields -> pure (name, [ty | (_, ty) <- fields]) -- ignore strictness/packedness metadata
    RecC          name fields -> pure (name, [ty | (_, _, ty) <- fields]) -- for records we also have field names to ignore
    InfixC field1 name field2 -> pure (name, [ty | (_, ty) <- [field1, field2]])
    _                         -> fail "We don't support any fancy constructors"


getConstructorBody' :: Name -> Q [Dec]
getConstructorBody' ty = do
  (name, types) <- getConstructorBody ty
  [d| x = $(pure (ConE name)) |]


deriveScore :: Name -> Q [Dec]
deriveScore ty = do
  (conName,paramTypes) <- getConstructorBody ty

  paramNames <- mapM (\pType -> newName $ "arg_" ) paramTypes
  let params = zip paramNames paramTypes
  [d|
      instance Score $(pure (ConT ty)) where
        score $(pure (ConP conName [] (map VarP paramNames ))) = $(foldl (\f (pn,pt) -> [| $f * ((score :: $(pure pt) -> Float) $(pure (VarE pn))) |]) [|1.0|] params)
    |]


-- deriveScore :: Name -> Q [Dec]
-- deriveScore ty = do
--   (conName,paramTypes) <- getConstructorBody ty

--   paramNames <- mapM (\pType -> newName $ "arg_" ) paramTypes
--   let params = zip paramNames paramTypes
--   [d|
--       instance Score $(pure (ConT ty)) where
--         score $(pure (ConP conName [] (map VarP paramNames ))) = $(foldl (\f (pn,pt) -> [| $f * ((score :: $(pure pt) -> Float) $(pure (VarE pn))) |]) [|1.0|] params)
--     |]

class Context c j where
  -- Initial context for the root judgement
  rootCtx :: Proxy j -> c
  -- Compute the child contexts for a node in the proof tree
  childContexts :: c -> Proof j -> [c]

instance Context Int j where
  rootCtx _ = 0
  childContexts n (Node _ ps) = map (const (n+1)) ps


deriveContext :: Name -> Name -> Q [Dec]
deriveContext ctx j = do
  (conName,paramTypes) <- getConstructorBody ctx
  (conName',paramTypes') <- getConstructorBody j

  paramNames <- mapM (\pType -> newName $ "arg_" ) paramTypes
  let params = zip paramNames paramTypes
  [d|
      instance Context $(pure (ConT ctx)) $(pure (ConT j)) where
        rootCtx $(pure (VarP $ mkName "pr")) = $(foldl (\f (pn,pt) -> [| $f (rootCtx $(pure $ VarE $ mkName "pr"))|]) (pure (ConE conName)) params)
        childContexts $(pure (ConP conName [] (map VarP paramNames ))) $(pure (VarP $ mkName "p"))
          = $(foldl (\f (pn,pt) -> [| $f (childContexts $(pure (VarE pn)) $(pure (VarE $ mkName "p"))) |]) (runQ [| $(zipn (length params)) $(pure $ ConE conName)|])  params) -- $(foldl (\f param -> [| $f (a :: $(pure param)) |]) (pure (ConE conName)) paramTypes)
    |]

{-
instance Context Car J1 where
  rootCtx _ = ConsCar 0 0
  childContexts (ConsCar y m) j = 
-}
  -- [d|
  --     instance Context $(pure (ConT ctx)) $(pure (ConT j)) where
  --       rootCtx _ = $(pure (ConE conName'))
  --       childContexts $(pure (ConP conName [] (map VarP paramNames ))) $(pure (VarP $ mkName "p"))
  --         = [ $(foldl (\f (pn,pt) -> [| $f (childContexts $(pure (VarE pn)) $(pure (VarE $ mkName "p"))) |]) (pure (ConE conName)) params) ]-- $(foldl (\f param -> [| $f (a :: $(pure param)) |]) (pure (ConE conName)) paramTypes)
  --   |]


zipn n = do
    vs <- replicateM n (newName "vs")
    [| \f ->
        $(lamE (map varP vs)
            [| getZipList $
                $(foldl
                    (\a b -> [| $a <*> $b |])
                    [| pure f |]
                    (map (\v -> [| ZipList $(varE v) |]) vs))
            |])
     |]