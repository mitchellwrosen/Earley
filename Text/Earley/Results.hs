-- | This module exposes the internals of the package: its API may change
-- independently of the PVP-compliant version number.
module Text.Earley.Results
  ( Results (..),
    lazyResults,
  )
where

import Control.Applicative
import Control.Monad
import Control.Monad.ST.Lazy
import Data.Coerce (coerce)
import Data.Foldable (fold)
import Data.STRef.Lazy

-------------------------------------------------------------------------------
-- Delayed results
-------------------------------------------------------------------------------

newtype Results s f a = Results
  { unResults :: ST s [f a]
  }
  deriving (Functor)

lazyResults :: ST s [f a] -> ST s (Results s f a)
lazyResults stas = mdo
  resultsRef <- newSTRef do
    as <- stas
    writeSTRef resultsRef (pure as)
    pure as
  pure (Results (join (readSTRef resultsRef)))

instance (Monad f, Traversable f) => Applicative (Results s f) where
  pure x = Results (pure [pure x])
  (<*>) = ap

instance (Monad f, Traversable f) => Alternative (Results s f) where
  empty = Results (pure [])
  Results xs <|> Results ys = Results ((<|>) <$> xs <*> ys)

instance (Monad f, Traversable f) => Monad (Results s f) where
  return = pure
  (>>=) :: forall a b. Results s f a -> (a -> Results s f b) -> Results s f b
  (>>=) = coerce @(ST s [f a] -> (a -> ST s [f b]) -> ST s [f b]) bind
    where
      bind :: ST s [f a] -> (a -> ST s [f b]) -> ST s [f b]
      bind mxs f = do
        xs <- mxs
        foldMapA g xs
        where
          g :: f a -> ST s [f b]
          g =
            fmap (fmap join . sequenceA) . traverse f

foldMapA :: (Applicative f, Monoid b, Traversable t) => (a -> f b) -> t a -> f b
foldMapA f xs =
  fold <$> traverse f xs
{-# INLINE foldMapA #-}

instance (Monad f, Traversable f) => Semigroup (Results s f a) where
  (<>) = (<|>)

instance (Monad f, Traversable f) => Monoid (Results s f a) where
  mempty = empty
  mappend = (<>)
