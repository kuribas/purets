{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Ast where
import qualified  Data.Text as Text
import Data.Scientific
import qualified Control.Unification as Uni
import GHC.Generics
import Control.Unification.IntVar

data Name = Name Text.Text Int
  deriving (Show, Eq, Ord)

data Literal =
  LInt Integer |
  LFloat Scientific 
  deriving (Generic, Ord, Eq)

instance Show Literal where
  show (LInt i) = show i
  show (LFloat f) = show f

data Kind =
  KindType |
  KindArr Kind Kind |
  KindVar
  deriving (Generic, Show, Eq, Ord)

-- Generic type representation.  The typevariables are needed to make
-- this work with different libraries.  b stands for a binding of
-- variables to a term, and t the
-- recursion type.
data Type t =
  TypeVar Name Kind |
  TypeArr t t  |
  TypeCon Name [t] |
  TypeApp t t |
  TypeForall [Name] (Type t)
  deriving (Generic, Show, Eq, Functor, Foldable, Traversable)

type TypeTerm = Uni.UTerm Type IntVar

-- | use Identity for foralls, since bindings are removed
instance Uni.Unifiable Type where
  zipMatch (TypeArr a1 b1) (TypeArr a2 b2) =
    Just $ TypeArr (Right (a1, a2)) (Right (b1, b2))
  zipMatch (TypeCon n1 as1) (TypeCon n2 as2)
    | n1 == n2 = Just $ TypeCon n1 $ zipWith (curry Right) as1 as2
  zipMatch (TypeApp a1 b1) (TypeApp a2 b2) =
    Just $ TypeApp (Right (a1, a2)) (Right (b1, b2))
  zipMatch (TypeForall names t1) t2 =
    TypeForall names <$> Uni.zipMatch t1 t2
  zipMatch t1 (TypeForall _names t2) =
    Uni.zipMatch t1 t2
  zipMatch (TypeVar n k) (TypeVar m _)
    | n == m = Just $ TypeVar n k
  zipMatch _ _ = Nothing
  
data Module t = Module [Declaration t]

-- | Expressions.  The t variable represent the kind of type.
data Expr t =
  Lit t Literal |
  Var t Name  |
  Lam t Name (Expr t) |
  App t (Expr t) (Expr t) |
  -- Explicit type application
  SetType Name TypeTerm (Expr t) | 
  Let t Name (Expr t) (Expr t) |
  -- type ascription
  Ascr t (Expr t)
  deriving (Generic, Show, Functor, Foldable, Traversable)

exprType :: Expr t -> t
exprType (Lit t _) = t
--exprType (SetType _ _ e) = exprType e
exprType (Var t _) = t
exprType (Lam t _ _) = t
exprType (App t _ _) = t
exprType (Let t _ _ _) = t
exprType (Ascr t _) = t

exprSetType :: Expr t -> t -> Expr t
exprSetType (Lit _ l) t = Lit t l
--exprSetType (SetType n term e) t = SetType n term (exprSetType e t)
exprSetType (Var _ n) t = Var t n
exprSetType (Lam _ e1 e2) t = Lam t e1 e2
exprSetType (App _ e1 e2) t = App t e1 e2
exprSetType (Let _ n e1 e2) t = Let t n e1 e2
exprSetType (Ascr _ e) t = Ascr t e

data Declaration t = Declaration Name TypeTerm (Expr t)
  deriving (Generic, Show, Functor, Foldable, Traversable)

