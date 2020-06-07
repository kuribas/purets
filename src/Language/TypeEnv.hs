{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language.TypeEnv (
  TypeEnv(..),
  empty,
  lookup,
  remove,
  extend,
  extends,
  merge,
  mergeEnvs,
  singleton,
  keys,
  fromList,
  toList,
) where

import Prelude hiding (lookup)

import Language.Ast
import Data.Foldable hiding (toList)
import qualified Data.Map as Map

-------------------------------------------------------------------------------
-- Typing Environment
-------------------------------------------------------------------------------

data TypeEnv = TypeEnv { types :: Map.Map Name TypeTerm}

empty :: TypeEnv
empty = TypeEnv Map.empty

extend :: TypeEnv -> (Name, TypeTerm) -> TypeEnv
extend env (x, s) = TypeEnv $ Map.insert x s (types env)

remove :: TypeEnv -> Name -> TypeEnv
remove (TypeEnv env) var = TypeEnv (Map.delete var env)

extends :: TypeEnv -> [(Name, TypeTerm)] -> TypeEnv
extends env xs = TypeEnv $ Map.union (Map.fromList xs) (types env)

lookup :: Name -> TypeEnv -> Maybe TypeTerm
lookup key (TypeEnv tys) = Map.lookup key tys

merge :: TypeEnv -> TypeEnv -> TypeEnv
merge (TypeEnv a) (TypeEnv b) = TypeEnv (Map.union a b)

mergeEnvs :: [TypeEnv] -> TypeEnv
mergeEnvs = foldl' merge empty

singleton :: Name -> TypeTerm -> TypeEnv
singleton x y = TypeEnv (Map.singleton x y)

keys :: TypeEnv -> [Name]
keys = Map.keys . types

fromList :: [(Name, TypeTerm)] -> TypeEnv
fromList = TypeEnv . Map.fromList 

toList :: TypeEnv -> [(Name, TypeTerm)]
toList = Map.toList . types

instance Monoid TypeEnv where
  mempty = empty

instance Semigroup TypeEnv where
  (<>) = merge
