-- | Context-free grammars.
module Text.Earley.Grammar
  ( Grammar (..),
    rule,
    runGrammar,
  )
where

import Control.Monad
import Control.Monad.Fix
import Text.Earley.Prod (Prod)

-- | A context-free grammar.
--
-- The type parameters are:
--
-- @a@: The return type of the grammar (often a 'Prod').
data Grammar s a where
  RuleBind :: Prod s t a -> (Prod s t a -> Grammar s b) -> Grammar s b
  FixBind :: (a -> Grammar s a) -> (a -> Grammar s b) -> Grammar s b
  Return :: a -> Grammar s a

instance Functor (Grammar s) where
  fmap f = \case
    RuleBind ps h -> RuleBind ps (fmap f . h)
    FixBind g h -> FixBind g (fmap f . h)
    Return x -> Return $ f x

instance Applicative (Grammar s) where
  pure = Return
  (<*>) = ap

instance Monad (Grammar s) where
  RuleBind ps f >>= k = RuleBind ps (f >=> k)
  FixBind f g >>= k = FixBind f (g >=> k)
  Return x >>= k = k x

instance MonadFix (Grammar s) where
  mfix f = FixBind f pure

-- | Create a new non-terminal by giving its production.
rule :: Prod s t a -> Grammar s (Prod s t a)
rule p = RuleBind p pure

-- | Run a grammar, given an action to perform on productions to be turned into non-terminals.
runGrammar ::
  forall b m r.
  (MonadFix m) =>
  (forall t a. Prod r t a -> m (Prod r t a)) ->
  Grammar r b ->
  m b
runGrammar r = go
  where
    go :: forall x. Grammar r x -> m x
    go = \case
      RuleBind p k -> do
        nt <- r p
        go (k nt)
      Return a -> pure a
      FixBind f k -> mdo
        a <- go (f a)
        go (k a)
