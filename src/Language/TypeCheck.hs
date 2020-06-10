{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
module Language.TypeCheck where

import Language.Ast
import Prelude hiding (lookup)
import Data.Functor
import Data.Maybe
import qualified Data.Map as Map
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Data.Bifunctor
import qualified Control.Unification.IntVar as Uni
import qualified Data.DList as DList
import Control.Unification.IntVar (IntVar)
import Control.Unification (UTerm(..))
import qualified Control.Unification as Uni

data Constraint = Match TypeTerm TypeTerm

data TypeError

data TypeVar = RigidVar Name
             | FreeVar IntVar

type VarTypeMap = Map.Map Name TypeTerm
type TypeMap = Map.Map Name TypeVar

data InferEnv = InferEnv
  { varTypes :: VarTypeMap
  , typeMap :: TypeMap }

newtype Infer a =
  Infer (ReaderT InferEnv 
         (WriterT (DList.DList Constraint)
           (Uni.IntBindingT Type
             (Except TypeError)))
          a)
  deriving (Functor, Applicative, Monad, MonadReader InferEnv)

liftBinding :: Uni.IntBindingT Type (Except TypeError) a -> Infer a
liftBinding = Infer . lift . lift

-- | Adding a single constraint.
addConstraint :: Constraint -> Infer ()
addConstraint = Infer . tell . DList.singleton

-- | Adding many constraints.
addConstraints :: [Constraint] -> Infer ()
addConstraints = Infer . tell . DList.fromList

getVarTypeMap :: Infer VarTypeMap
getVarTypeMap = varTypes <$> Infer ask

getTypeMap :: Infer TypeMap
getTypeMap = typeMap <$> Infer ask

lookupVarType :: Name -> Infer (Maybe TypeTerm)
lookupVarType name = Infer $ asks $ Map.lookup name . varTypes

lookupType :: Name -> Infer (Maybe TypeVar)
lookupType name = Infer $ asks $ Map.lookup name . typeMap 

extendVar :: Name -> TypeTerm -> Infer a -> Infer a
extendVar name tp (Infer m) = Infer $ local extend m
  where extend env = env { varTypes = Map.insert name tp $ varTypes env}

withLocalTypeMap :: TypeMap -> Infer a -> Infer a
withLocalTypeMap mp = local $ \env -> env { typeMap = mp }

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

typeVarTerm :: TypeVar -> TypeTerm
typeVarTerm (RigidVar n) = UTerm $ TypeVar n KindVar
typeVarTerm (FreeVar i) = UVar i

-- | substitute a unique variable name or fresh variable for a type variable
substTypeVar :: TypeMap -> Name -> Kind -> Infer TypeTerm
substTypeVar subst n k = case Map.lookup n subst of
  Just (RigidVar name) -> pure $ UTerm $ TypeVar name k
  Just (FreeVar var) -> pure $ UVar var
  Nothing -> pure $ UTerm $ TypeVar n k

data UnPolyState = USRigid | USFresh | USLambda | USReplace

unPolyNextState :: UnPolyState -> UnPolyState
-- alternating rigid/fresh
unPolyNextState USRigid = USFresh
-- alternating fresh/rigid
unPolyNextState USFresh = USRigid
-- rigid for first level, substitution for other levels.
unPolyNextState USLambda = USReplace
-- perform only existing substitutions
unPolyNextState USReplace = USReplace
  
unPoly :: UnPolyState -> TypeMap -> TypeTerm -> Infer (TypeTerm, TypeMap) 
unPoly _ subst (UVar v) = pure (UVar v, subst)
unPoly _ subst (UTerm (TypeVar n k)) =
  (,subst) <$> substTypeVar subst n k
unPoly upState subst (UTerm (TypeArr t1 t2)) = do
  arg <- fst <$> unPoly (unPolyNextState upState) subst t1
  ret <- fst <$> unPoly upState subst t2
  pure (UTerm (TypeArr arg ret), subst)
unPoly _ subst (UTerm (TypeCon n t)) = pure (UTerm (TypeCon n t), subst)
unPoly upState subst (UTerm (TypeApp t1 t2)) = do
  rigid1 <- fst <$> unPoly upState subst t1
  rigid2 <- fst <$> unPoly upState subst t2
  pure (UTerm (TypeApp rigid1 rigid2), subst)
unPoly upState subst (UTerm (TypeForall names tp)) =
  case upState of
    USFresh -> do
      newNames <- mapM (\name -> (name,) <$> freshVar) names
      let newSubst = foldl (\s (name,fresh) ->
                              Map.insert name (FreeVar fresh) s)
                     subst newNames
      unPoly USRigid newSubst (UTerm tp)
    USReplace -> do
      let newSubst = foldl (flip Map.delete) subst names
      fst <$> unPoly upState newSubst (UTerm tp) >>= \case
        UTerm newTp -> pure (UTerm $ TypeForall names newTp, subst)
        -- drop the forall if the body is a unification variable, as
        -- it's not needed anyway in that case
        uvar -> pure (uvar, subst)
    _ -> do
      newNames <- mapM (\name -> (name,) <$> freshName name)
                  names
      let newSubst = foldl (\s (name,fresh) -> Map.insert
                             name (RigidVar fresh) s)
                     subst newNames
      fst <$> unPoly upState newSubst (UTerm tp) >>= \case
        UTerm newTp -> pure (UTerm (TypeForall (map snd newNames) newTp),
                             newSubst)
        uvar -> pure (uvar, newSubst)

withUnPoly :: UnPolyState -> TypeTerm -> (TypeTerm -> Infer a) -> Infer a
withUnPoly upState t f = do
  env <- getTypeMap
  (t2, newEnv) <- unPoly upState env t
  withLocalTypeMap newEnv (f t2)

withLambdaType :: TypeTerm -> (TypeTerm -> Infer a) -> Infer a
withLambdaType = withUnPoly USLambda

withCheckedType :: TypeTerm -> (TypeTerm -> Infer a) -> Infer a
withCheckedType = withUnPoly USRigid

inferredType :: TypeTerm -> Infer TypeTerm
inferredType t = withUnPoly USFresh t pure

-- | Run the inference monad
runInfer :: InferEnv -> Infer TypeTerm
         -> Either TypeError (TypeTerm, [Constraint])
runInfer env (Infer m) =
  runExcept $ Uni.evalIntBindingT $
  fmap (second DList.toList) $
  runWriterT $ runReaderT m env

inferPoly :: Maybe TypeTerm -> Infer (Expr TypeTerm) -> Infer (Expr TypeTerm)
inferPoly Nothing inf = inf
inferPoly (Just given) inf = withCheckedType given $ \checked -> do
  infExpr <- inf
  checked `matchWith` exprType infExpr
  inferred <- inferredType given
  pure $ infExpr $> inferred

infer :: Expr (Maybe TypeTerm)  -> Infer (Expr TypeTerm)
infer (Lit given (LInt i)) =
  inferPoly given $ pure $
  Lit (UTerm (TypeCon (Name "int" 0) [])) (LInt i)

infer (Lit given (LFloat f)) =
  inferPoly given $ pure $
  Lit (UTerm (TypeCon (Name "float" 0) [])) (LFloat f)

infer (Lit given (LList l)) =
  inferPoly given $ do
  t <- freshTerm
  pure $ Lit (UTerm (TypeApp (UTerm (TypeCon (Name "list" 0) [])) t)) (LList l)

infer (Var given name) =
  lookupVarType name >>= \case 
    Nothing -> error "name not found"
    Just inferred -> inferPoly given $ pure $ Var inferred name

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
    inferLam1 name expr givenType =
      withLambdaType givenType $ \inferred ->
      splitArr name expr inferred Nothing

    -- split the arrow type from outer in argument and body, and match
    -- agains the expression
    splitArr :: Name -> Expr (Maybe TypeTerm) -> TypeTerm -> Maybe TypeTerm
             -> Infer (Expr TypeTerm)
    splitArr name expr outer inner =
      case outer of
        UTerm (TypeArr t1 t2) -> inferLam2 name expr inner t1 t2
        _ -> do t1 <- freshTerm
                t2 <- freshTerm
                outer `matchWith` UTerm (TypeArr t1 t2)
                inferLam2 name expr inner t1 t2
                
    inferLam2 :: Name -> Expr (Maybe TypeTerm) -> Maybe TypeTerm -> TypeTerm
              -> TypeTerm
              -> Infer (Expr TypeTerm)
    -- argument type and body type are given
    inferLam2 name expr Nothing argType returnType = do
      subExpr <- extendVar name argType $
        case expr of
          Lam given name2 expr2 -> splitArr name2 expr2 returnType given
          t -> do subExpr <- infer t
                  let subExprType = exprType subExpr
                  returnType `matchWith` subExprType
                  pure subExpr
      pure $ Lam (UTerm (TypeArr argType returnType)) name subExpr
          
    -- argument type, body type, and an inner type are given.
    inferLam2 name expr (Just given) argType returnType = do
      innerExpr <- inferLam1 name expr given
      let outerType = UTerm (TypeArr argType returnType)
      outerType `matchWith` exprType innerExpr
      pure $ innerExpr $> outerType

-- | tp should not be polymorphic
infer (SetType name tp expr) =
  lookupType name >>= \case
    Nothing -> error $ "unkown type" ++ show name
    Just tp2 -> do
      tp `matchWith` typeVarTerm tp2
      infer expr
                              
infer (App given fun args) = inferPoly given $ do
  funInf <- infer fun
  argsInf <- infer args
  ret <- freshTerm
  UTerm (TypeArr (exprType argsInf) ret) `matchWith` exprType funInf
  pure $ App ret funInf argsInf

infer (Let given name expr1 expr2) = inferPoly given $ do
  infExpr1 <- infer expr1
  extendVar name (fromMaybe (exprType infExpr1) (exprType expr1)) $
    infer expr2
      
infer (Ascr given expr) = inferPoly given $ infer expr
