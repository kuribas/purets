{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.TypeCheck where

import Language.Ast
import Language.TypeEnv

import Prelude hiding (lookup)
import Data.Maybe
import Data.Functor
import Data.Traversable
import Control.Applicative
import Data.Foldable
import qualified Data.Text as Text
import qualified Data.Map as Map
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import Data.Bifunctor
import qualified Control.Unification.IntVar as Uni
import qualified Data.DList as DList
import Control.Unification.IntVar (IntVar)
import Control.Unification (UTerm(..))
import qualified Control.Unification as Uni

data Constraint = Match TypeTerm TypeTerm

data TypeError

newtype Infer a =
  Infer (ReaderT TypeEnv (WriterT (DList.DList Constraint)
                          (Uni.IntBindingT Type (Except TypeError)))
         a)
  deriving (Functor, Applicative, Monad)

liftBinding :: Uni.IntBindingT Type (Except TypeError) a -> Infer a
liftBinding = Infer . lift . lift

-- | Adding a single constraint.
addConstraint :: Constraint -> Infer ()
addConstraint = Infer . tell . DList.singleton

-- | Adding many constraints.
addConstraints :: [Constraint] -> Infer ()
addConstraints = Infer . tell . DList.fromList

getEnv :: Infer TypeEnv
getEnv = Infer ask

localEnv :: (TypeEnv -> TypeEnv) -> Infer a -> Infer a
localEnv f (Infer e) = Infer $ local f e

extendEnv :: Name -> TypeTerm -> Infer a -> Infer a
extendEnv name tp = localEnv (`extend` (name, tp))

matchWith :: TypeTerm -> TypeTerm -> Infer ()
matchWith t1 t2 = addConstraint $ Match t1 t2

freshName :: Name -> Infer Name
freshName (Name s _) = do
  Uni.IntVar i <- liftBinding Uni.freeVar
  pure $ Name s i

freshVar :: Infer Uni.IntVar
freshVar = liftBinding Uni.freeVar

freshTerm :: Infer TypeTerm
freshTerm = UVar <$> freshVar 

bindTerm :: TypeTerm -> Infer TypeTerm
bindTerm = fmap UVar . liftBinding . Uni.newVar

-- | substitute a unique variable name or fresh variable for a type variable
substTypeVar :: Map.Map Name (Either Name IntVar) -> Name -> Kind
             -> Infer TypeTerm
substTypeVar subst n k = case Map.lookup n subst of
  Just (Left name) -> pure $ UTerm $ TypeVar name k
  Just (Right var) -> pure $ UVar var
  Nothing -> pure $ UTerm $ TypeVar n k
             
-- | Create a rigid type, by making all variables unique.  Rigid
-- variables can only match itself. It alternates with makeFreshType
-- for function inputs.  The TypeTerm should not have any bound
-- unification variables.
makeRigidType :: Map.Map Name (Either Name IntVar) -> TypeTerm
              -> Infer TypeTerm
makeRigidType _ (UVar v) = pure $ UVar v
makeRigidType subst (UTerm (TypeVar n k)) =
  substTypeVar subst n k
makeRigidType subst (UTerm (TypeArr t1 t2)) =
  UTerm <$> (TypeArr <$> makeFreshType subst t1 <*> makeRigidType subst t2)
makeRigidType _subst (UTerm (TypeCon n t)) = pure $ UTerm (TypeCon n t)
makeRigidType subst (UTerm (TypeApp t1 t2)) = 
  UTerm <$> (TypeApp <$> makeFreshType subst t1 <*> makeFreshType subst t2)
makeRigidType subst (UTerm (TypeForall names tp)) = do
  newNames <- mapM (\name -> (name,) <$> freshName name) names
  let newSubst = foldl (\s (name,fresh) -> Map.insert name (Left fresh) s)
                 subst newNames
  UTerm newTp <- makeRigidType newSubst (UTerm tp)
  pure $ UTerm (TypeForall (map snd newNames) newTp)

-- | Make a polymorphic type term monomorphic, by creating fresh
-- bindings for each type variable.  The term should not have any
-- bound unification variables.
makeFreshType ::  Map.Map Name (Either Name IntVar) -> TypeTerm
              -> Infer TypeTerm
makeFreshType _subst (UVar v) = pure $ UVar v
makeFreshType subst (UTerm (TypeVar n k)) =
  substTypeVar subst n k
makeFreshType subst (UTerm (TypeArr t1 t2)) =
  UTerm <$> (TypeArr <$> makeRigidType subst t1 <*> makeFreshType subst t2)
makeFreshType _subst (UTerm (TypeCon n t)) = pure $ UTerm (TypeCon n t)
makeFreshType subst (UTerm (TypeApp t1 t2)) = 
  UTerm <$> (TypeApp <$> makeFreshType subst t1 <*> makeFreshType subst t2)
makeFreshType subst (UTerm (TypeForall names tp)) = do
  newNames <- mapM (\name -> (name,) <$> freshVar) names
  let newSubst = foldl (\s (name,fresh) -> Map.insert name (Right fresh) s)
                 subst newNames
  makeRigidType newSubst (UTerm tp)

-- | Run the inference monad
runInfer :: TypeEnv -> Infer TypeTerm
         -> Either TypeError (TypeTerm, [Constraint])
runInfer env (Infer m) =
  runExcept $ Uni.evalIntBindingT $
  fmap (second DList.toList) $
  runWriterT $ runReaderT m env

unPoly :: Maybe TypeTerm -> Infer (TypeTerm, TypeTerm)
unPoly Nothing = do
  v <- UVar <$> freshVar
  pure (v, v)
unPoly (Just t) = do
  rigid <- bindTerm =<< makeRigidType Map.empty t
  fresh <- bindTerm =<< makeFreshType Map.empty t
  pure (rigid, fresh)

infer :: Expr (Maybe TypeTerm)  -> Infer (Expr TypeTerm)
infer (Lit given (LInt i)) = do
  (rigid, fresh) <- unPoly given
  rigid `matchWith` UTerm (TypeCon (Name "int" 0) [])
  pure $ Lit fresh (LInt i)

infer (Var given name) = do
  env <- getEnv
  case lookup name env of
    Nothing -> error "name not found"
    Just tp -> do
      mono <- makeFreshType Map.empty tp
      (rigid, fresh) <- unPoly given
      rigid `matchWith` mono
      pure $ Var fresh name

infer (Lam mbGiven0 name0 expr0) =
  case mbGiven0 of
    Nothing -> do t1 <- freshTerm
                  t2 <- freshTerm
                  inferLam2 name0 expr0 Nothing t1 t2
    Just given -> inferLam1 name0 expr0 given
  where
    -- only one (possibly polymorphic) type is given
    inferLam1 :: Name -> Expr (Maybe TypeTerm) -> TypeTerm
              -> Infer (Expr TypeTerm)
    inferLam1 name expr givenType = do
      fresh <- makeFreshType Map.empty givenType
      splitArr name expr fresh Nothing

    -- | split the arrow type from outer in argument and body, and match
    -- agains the expression
    splitArr :: Name -> Expr (Maybe TypeTerm) -> TypeTerm -> Maybe TypeTerm
             -> Infer (Expr TypeTerm)
    splitArr name expr outer inner =
      case outer of
        UTerm (TypeArr t1 t2) -> inferLam2 name expr inner t1 t2
        _ -> do t1 <- freshTerm
                t2 <- freshTerm
                t1 `matchWith` UTerm (TypeArr t1 t2)
                inferLam2 name expr Nothing t1 t2
                
    inferLam2 :: Name -> Expr (Maybe TypeTerm) -> Maybe TypeTerm -> TypeTerm
              -> TypeTerm
              -> Infer (Expr TypeTerm)
    -- | argument type and body type are given
    inferLam2 name expr Nothing argType returnType = do
      subExpr <- extendEnv name argType $ do
        case expr of
          Lam tp name2 expr2 -> splitArr name2 expr2 returnType tp
          t -> do subExpr <- infer t
                  let subExprType = exprType subExpr
                  subExprType `matchWith` returnType
                  pure subExpr
      pure $ Lam (UTerm (TypeArr argType returnType)) name subExpr
          
    -- | argument type, body type, and an inner type are given.
    inferLam2 name expr (Just tp) argType returnType = do
      innerExpr <- inferLam1 name expr tp
      let innerExprType = exprType innerExpr
          outerType = UTerm (TypeArr argType returnType)
      innerExprType `matchWith` outerType
      pure $ innerExpr $> outerType
