{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Language.TypeCheck where

import Language.Ast
import Control.Unification.IntVar
import Prelude hiding (lookup)
import qualified Data.Text as Text
import Data.Text (Text)
import Data.Functor
import Data.Maybe
import qualified Data.Map as Map
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Functor.Identity
import Data.List (foldl')
import Data.Bifunctor
import Control.Unification (UTerm(..))
import qualified Control.Unification as Uni
import qualified Control.Unification.Types as Uni

data Constraint = Match TypeTerm TypeTerm
  deriving (Show)

data TypeError = UnknownVar Text
               | UnknownTypeVar Text
               | OccursFailure IntVar TypeTerm
               | MismatchFailure (Type TypeTerm) (Type TypeTerm)
  deriving (Show)

-- | a fresh or skolem variable for type checking
data TypeVar = SkolemVar Name
             | FreeVar IntVar

-- | A map from term variables to types.
type VarTypeMap = Map.Map Name TypeTerm
-- | A map from type variables to fresh or skolem variables.
type TypeMap = Map.Map Name TypeVar

data InferEnv = InferEnv
  { varTypes :: VarTypeMap
  , typeMap :: TypeMap }

data InferState = InferState
  { inferConstraints :: [Constraint]
  , inferTypeErrors :: [TypeError]
  } deriving (Show)

instance Semigroup InferState where
  InferState c1 e1 <> InferState c2 e2 = InferState (c1 <> c2) (e1 <> e2)

instance Monoid InferState where
  mempty = InferState [] []

emptyInferState :: InferState
emptyInferState = InferState [] [] 

emptyEnv :: InferEnv
emptyEnv = InferEnv { varTypes = Map.empty
                    , typeMap = Map.empty
                    }

-- | The Infer monad.
newtype Infer a =
  Infer (ReaderT InferEnv
         (StateT InferState (IntBindingT Type Identity))
          a)
  deriving (Functor, Applicative, Monad)

liftBinding :: IntBindingT Type Identity a -> Infer a
liftBinding = Infer . lift . lift

-- | Adding a single constraint.
addConstraint :: Constraint -> Infer ()
addConstraint c = Infer $ modify $ \s ->
  s {inferConstraints = c:inferConstraints s}
  
-- | Adding many constraints.
addConstraints :: [Constraint] -> Infer ()
addConstraints cs = Infer $ modify $ \s ->
  s {inferConstraints = cs ++ inferConstraints s}

-- | Adding a single constraint.
addTypeError :: TypeError -> Infer ()
addTypeError e = Infer $ modify $ \s ->
  s {inferTypeErrors = e:inferTypeErrors s}


getVarTypeMap :: Infer VarTypeMap
getVarTypeMap = varTypes <$> Infer ask

getTypeMap :: Infer TypeMap
getTypeMap = typeMap <$> Infer ask

lookupVarType :: Name -> Infer (Maybe TypeTerm)
lookupVarType name = Infer $ asks $ Map.lookup name . varTypes

lookupType :: Name -> Infer (Maybe TypeVar)
lookupType name = Infer $ asks $ Map.lookup name . typeMap 

-- | Evaluate the given Infer monad in an extended variable
-- environment
extendVar :: Name -> TypeTerm -> Infer a -> Infer a
extendVar name tp (Infer m) = Infer $ local extend m
  where extend env = env { varTypes = Map.insert name tp $ varTypes env}

withLocalTypeMap :: TypeMap -> Infer a -> Infer a
withLocalTypeMap mp (Infer inf) =
  Infer $ local (\env -> env { typeMap = mp }) inf

matchWith :: TypeTerm -> TypeTerm -> Infer ()
matchWith expected actual = do
  r <- liftBinding $ runExceptT $ Uni.unify expected actual
  case r of
    Left (Uni.OccursFailure v t) -> addTypeError (OccursFailure v t)
    Left (Uni.MismatchFailure t1 t2) -> addTypeError (MismatchFailure t1 t2)
    Right _ -> pure ()

freshName :: Name -> Infer Name
freshName (Name s _) = do
  IntVar i <- liftBinding Uni.freeVar
  pure $ Name s i

freshVar :: Infer IntVar
freshVar = liftBinding Uni.freeVar

freshTerm :: Infer TypeTerm
freshTerm = UVar <$> freshVar 

bindTerm :: TypeTerm -> Infer TypeTerm
bindTerm = fmap UVar . liftBinding . Uni.newVar

typeVarTerm :: TypeVar -> TypeTerm
typeVarTerm (SkolemVar n) = UTerm $ TypeVar n KindVar
typeVarTerm (FreeVar i) = UVar i

-- | substitute a unique variable name or fresh variable for a type variable
substTypeVar :: TypeMap -> Name -> Kind -> Infer TypeTerm
substTypeVar subst n k = case Map.lookup n subst of
  Just (SkolemVar name) -> pure $ UTerm $ TypeVar name k
  Just (FreeVar var) -> pure $ UVar var
  Nothing -> pure $ UTerm $ TypeVar n k

data UnPolyState = UPSSkolem | UPSFresh | UPSLambda | UPSReplace

-- | How to replace typevariables in `unPoly`.
unPolyNextState :: UnPolyState -> UnPolyState
-- | alternating skolem/fresh
unPolyNextState UPSSkolem = UPSFresh
-- | alternating fresh/skolem
unPolyNextState UPSFresh = UPSSkolem
-- | skolem for first level, substitution for other levels.
unPolyNextState UPSLambda = UPSReplace
-- | perform only existing substitutions
unPolyNextState UPSReplace = UPSReplace

-- | remove polymorphic variables by replacing them with either a
-- skolem or a logic variable (in the Infer monad).  The UnPolyState
-- determines how to do substitution of foralls.
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
  skolem1 <- fst <$> unPoly upState subst t1
  skolem2 <- fst <$> unPoly upState subst t2
  pure (UTerm (TypeApp skolem1 skolem2), subst)
unPoly upState subst (UTerm (TypeForall names tp)) =
  case upState of
    UPSFresh -> do
      -- create a fresh variable for each name variable in the forall
      newNames <- traverse (\name -> (name,) <$> freshVar) names
      let newSubst = foldl' (\s (name,fresh) ->
                              Map.insert name (FreeVar fresh) s)
                     subst newNames
      unPoly upState newSubst (UTerm tp)
    UPSReplace -> do
      let newSubst = foldl' (flip Map.delete) subst names
      unPoly upState newSubst (UTerm tp) >>= \case
        (UTerm newTp, _) -> pure (UTerm $ TypeForall names newTp, subst)
        -- drop the forall if the body is a unification variable, as
        -- it's not needed anyway in that case
        (uvar, _) -> pure (uvar, subst)
    _ -> do
      newNames <- traverse (\name -> (name,) <$> freshName name)
                  names
      let newSubst = foldl' (\s (name,fresh) ->
                              Map.insert name (SkolemVar fresh) s)
                     subst newNames
      unPoly upState newSubst (UTerm tp) >>= \case
        (UTerm newTp, _) -> pure (UTerm (TypeForall (map snd newNames) newTp),
                             newSubst)
        (uvar, _) -> pure (uvar, newSubst)

-- | create a new environment with the polymorphic variables
-- substituted by fresh variables, then evaluate the function in the
-- modified environment.
withUnPoly :: UnPolyState -> TypeTerm -> (TypeTerm -> Infer a) -> Infer a
withUnPoly upState t f = do
  env <- getTypeMap
  (t2, newEnv) <- unPoly upState env t
  withLocalTypeMap newEnv (f t2)

-- | substitute polymorphic variables for checking a lambda type.
-- This only substitutes on toplevel, and leaves polymorphic arguments
-- alone.  Then pass the updated term to a function in a modified
-- environment.
withLambdaType :: TypeTerm -> (TypeTerm -> Infer a) -> Infer a
withLambdaType = withUnPoly UPSLambda

-- | substitute polymorphic variables for checking a type, then pass
-- the updated term to a function in a modified environment.
withCheckedType :: TypeTerm -> (TypeTerm -> Infer a) -> Infer a
withCheckedType = withUnPoly UPSSkolem

-- | create monomorphic version of polymorphic type, with fresh
-- variables for inferring a type.
inferredType :: TypeTerm -> Infer TypeTerm
inferredType t = withUnPoly UPSFresh t pure

-- | Run the inference monad
runInfer :: InferEnv -> Infer a
         -> (a, InferState)
runInfer env (Infer m) =
  runIdentity $ evalIntBindingT $ flip runStateT emptyInferState $
  runReaderT m env

runInferApply :: InferEnv -> Infer (Expr TypeTerm)
              -> (Expr TypeTerm, InferState)
runInferApply env i = runInfer env $ i >>= applyExprBindings

-- | apply all bindings to an expression.  If occursFailure error
-- happens, the original expression is returned (which should likely
-- be ignored)
applyExprBindings :: Expr TypeTerm -> Infer (Expr TypeTerm)
applyExprBindings expr = do
  infExpr <- liftBinding $ runExceptT $ Uni.applyBindingsAll expr
  case infExpr of
    Left (Uni.OccursFailure v t) -> do
      addTypeError (OccursFailure v t)
      pure expr
    Left (Uni.MismatchFailure t1 t2) -> do
      addTypeError (MismatchFailure t1 t2)
      pure expr
    Right res -> pure res
  
-- | if the expression is a forall, return a monomorphic version with
-- fresh variables.
inferForall :: Infer (Expr TypeTerm) -> Infer (Expr TypeTerm)
inferForall inf = do
  infExpr <- inf
  inferred <- inferredType $ exprType infExpr
  pure $ exprSetType infExpr inferred
  
-- | check if the polymorphic type matches the type of the term.  Then
-- return a monomorphic version with fresh variables. Note that inf
-- should be monomorphic (not a forall).
ascribePoly :: TypeTerm -> Infer (Expr TypeTerm) -> Infer (Expr TypeTerm)
ascribePoly given inf = withCheckedType given $ \checked -> do
  infExpr <- inf
  checked `matchWith` exprType infExpr
  inferred <- inferredType given
  pure $ exprSetType infExpr inferred

ascribePolyMaybe :: Maybe TypeTerm -> Infer (Expr TypeTerm)
                 -> Infer (Expr TypeTerm)
ascribePolyMaybe Nothing inf = inf
ascribePolyMaybe (Just given) inf = ascribePoly given inf

intType, floatType :: TypeTerm
intType = UTerm $ TypeCon (Name "int" 0) []
floatType = UTerm $ TypeCon (Name "float" 0) []

infer :: Expr (Maybe TypeTerm) -> Infer (Expr TypeTerm)
infer (Lit given (LInt i)) =
  ascribePolyMaybe given $ pure $ Lit intType (LInt i)

infer (Lit given (LFloat f)) =
  ascribePolyMaybe given $ pure $ Lit floatType (LFloat f)

infer (Var given name@(Name varName _)) = do
  varTp <- lookupVarType name
  infExpr <- case varTp of
    Just found -> inferredType found
    Nothing -> do
      addTypeError $ UnknownVar varName
      freshTerm -- return just a fresh variable.
  ascribePolyMaybe given $ pure $ Var infExpr name

-- infering lambdas is more complicated, because we want to support
-- polymorphic arguments, and we have different ways to assign a
-- polymorphic type to an argument
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
infer (SetType name tp expr) = do
  mbTp <- lookupType name
  term <- case mbTp of
    Nothing -> do
      addTypeError $ UnknownTypeVar $ Text.pack $ show name
      a <- freshName $ Name "a" 0
      pure $ UTerm $ TypeForall [name] (TypeVar a KindType)
    Just found -> pure $ typeVarTerm found
  tp `matchWith` term
  infer expr
                              
infer (App given fun args) = ascribePolyMaybe given $ do
  funInf <- infer fun
  argsInf <- infer args
  ret <- freshTerm
  UTerm (TypeArr (exprType argsInf) ret) `matchWith` exprType funInf
  pure $ App ret funInf argsInf

infer (Let given name expr1 expr2) = ascribePolyMaybe given $ do
  infExpr1 <- infer expr1
  extendVar name (fromMaybe (exprType infExpr1) (exprType expr1)) $
    infer expr2
      
infer (Ascr given expr) = ascribePolyMaybe given $ infer expr

inferModule :: TypeMap
            -> Module (Maybe TypeTerm)
            -> (Module TypeTerm, InferState)
inferModule globalTypes (Module decls) =
  let inferDecl :: Declaration (Maybe TypeTerm)
                -> ([Declaration TypeTerm], InferState)
      inferDecl (Declaration name tp expr) =
        runInfer (InferEnv Map.empty globalTypes) $ do
        checkedExpr <- ascribePoly tp $ infer expr
        appliedExpr <- applyExprBindings $ exprSetType checkedExpr tp
        pure $ [Declaration name tp appliedExpr]
  in first Module $ foldMap inferDecl decls
