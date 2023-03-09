-- File generated by the BNF Converter (bnfc 2.9.4).

{-# LANGUAGE PatternSynonyms #-}

-- | The abstract syntax of language Parser.

module Lang.AbsParser where

import Prelude (Char, Double, String)
import qualified Prelude as C
  ( Eq, Ord, Show, Read
  , Int, Maybe(..)
  )

data SCPL = SCPLPROG [Defn]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Defn = DEFN PIdent Stmt
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Stmt
    = CASESTMT Exp [CaseTerm]
    | IFSTMT Exp Stmt Stmt
    | BARESTMT Exp
    | ELet Let LetInStmt Stmt
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Let = LET | LRec
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data CaseTerm = CASE_STMT CasePattern Stmt
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data LetInStmt = LET_IN_STMT PIdent Exp
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Type = TYPEARROW TypeN Type | TYPENext TypeN
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data TypeN
    = TYPEUNIT TokUnit
    | TYPECONST_VAR UIdent
    | TYPELIST Type
    | TYPEPROD [Type]
    | TYPEBRACKET Type
    | CONST_TYPE ConstantType
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data CasePattern = TRUE_PATTERN | FALSE_PATTERN
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Exp
    = EInt PInteger
    | ETrue
    | EFalse
    | EVar PIdent
    | EString String
    | EList [Exp]
    | EApp Exp Exp
    | ENeg Exp
    | CONSTERM Exp Exp
    | EAPPEND Exp Exp
    | EMul Exp Exp
    | EDiv Exp Exp
    | EAdd Exp Exp
    | ESub Exp Exp
    | ELt Exp Exp
    | EGt Exp Exp
    | ELEq Exp Exp
    | EGEq Exp Exp
    | EEq Exp Exp
    | ENEq Exp Exp
    | EAnd Exp Exp
    | EOr Exp Exp
    | ELambda [PIdent] Stmt
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data TypeAnnotation = TYPEANNOTATION Type | TYPEANNOTATION_EMPTY
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data ConstantType
    = INTEGER PInteger | STRING String | CHAR Char | DOUBLE Double
  deriving (C.Eq, C.Ord, C.Show, C.Read)

newtype TokUnit = TokUnit ((C.Int, C.Int), String)
  deriving (C.Eq, C.Ord, C.Show, C.Read)

newtype UIdent = UIdent ((C.Int, C.Int), String)
  deriving (C.Eq, C.Ord, C.Show, C.Read)

newtype PIdent = PIdent ((C.Int, C.Int), String)
  deriving (C.Eq, C.Ord, C.Show, C.Read)

newtype PInteger = PInteger ((C.Int, C.Int), String)
  deriving (C.Eq, C.Ord, C.Show, C.Read)

-- | Start position (line, column) of something.

type BNFC'Position = C.Maybe (C.Int, C.Int)

pattern BNFC'NoPosition :: BNFC'Position
pattern BNFC'NoPosition = C.Nothing

pattern BNFC'Position :: C.Int -> C.Int -> BNFC'Position
pattern BNFC'Position line col = C.Just (line, col)

-- | Get the start position of something.

class HasPosition a where
  hasPosition :: a -> BNFC'Position

instance HasPosition TokUnit where
  hasPosition (TokUnit (p, _)) = C.Just p

instance HasPosition UIdent where
  hasPosition (UIdent (p, _)) = C.Just p

instance HasPosition PIdent where
  hasPosition (PIdent (p, _)) = C.Just p

instance HasPosition PInteger where
  hasPosition (PInteger (p, _)) = C.Just p

