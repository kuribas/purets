{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | replacement for Control.Unification.IntVar that supports MonadError
module Language.IntBinding where
import qualified Control.Unification as Uni
import Control.Monad.State
import qualified Data.IntMap as IntMap
import Control.Unification (UTerm(..))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer.Strict

newtype IntVar = IntVar Int
  deriving (Eq, Show)

instance Uni.Variable IntVar where
  getVarID (IntVar i) = i

  
data BindingState t = BindingState
  { nextFreeVar :: {-# UNPACK #-} !Int
  , varBindings :: IntMap.IntMap (UTerm t IntVar)
  }

-- | Binding monad using integers.  Create our own since the one from
-- Control.Unification.IntVar doesn't support MonadExcept.
newtype IntBindingT t m a = IntBindingT {
  getBinding :: StateT (BindingState t) m a}
  deriving (Functor, Applicative, Monad, MonadTrans, MonadError e,
            MonadReader r, MonadWriter w)

evalIntBindingT :: Monad m => IntBindingT t m a -> m a
evalIntBindingT (IntBindingT stateM) =
  evalStateT stateM $ BindingState 0 IntMap.empty

instance (Monad m, Uni.Unifiable t) =>
         Uni.BindingMonad t IntVar (IntBindingT t m) where
  lookupVar (IntVar var) = IntBindingT $ gets (IntMap.lookup var . varBindings)
  freeVar = IntBindingT $ do
    ibs <- get
    let v = nextFreeVar ibs
    if  v == maxBound
      then error "freeVar: no more variables!"
      else do
      put $ ibs { nextFreeVar = v+1 }
      return $ IntVar v
  newVar t = IntBindingT $ do
        ibs <- get
        let v = nextFreeVar ibs
        if  v == maxBound
            then error "newVar: no more variables!"
            else do
                let bs' = IntMap.insert v t (varBindings ibs)
                put $ ibs { nextFreeVar = v+1, varBindings = bs' }
                return $ IntVar v
  bindVar (IntVar v) t = IntBindingT $ do
    ibs <- get
    let bs' = IntMap.insert v t (varBindings ibs)
    put $ ibs { varBindings = bs' }
