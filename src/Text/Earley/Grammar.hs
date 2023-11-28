-- | Context-free grammars.
module Text.Earley.Grammar
  ( Prod (..),
    terminal,
    nonTerminal,
    (<?>),
    alts,
    Grammar (..),
    rule,
    runGrammar,
  )
where

import Control.Applicative
import Control.Monad
import Control.Monad.Fix
import Data.Semigroup
import Data.String (IsString (..))
import Data.Text (Text)

infixr 0 <?>

-- | A production.
--
-- The type parameters are:
--
-- @a@: The return type of the production.
--
-- @t@ for terminal: The type of the terminals that the production operates
-- on.
--
-- @r@ for rule: The type of a non-terminal. This plays a role similar to the
-- @s@ in the type @ST s a@.  Since the 'parser' function expects the @r@ to be
-- universally quantified, there is not much to do with this parameter other
-- than leaving it universally quantified.
--
-- As an example, @'Prod' r 'String' 'Char' 'Int'@ is the type of a production that
-- returns an 'Int', operates on (lists of) characters and reports 'String'
-- names.
--
-- Most of the functionality of 'Prod's is obtained through its instances, e.g.
-- 'Functor', 'Applicative', and 'Alternative'.
data Prod r t a where
  -- Applicative.
  Terminal :: !(t -> Maybe a) -> !(Prod r t (a -> b)) -> Prod r t b
  NonTerminal :: !(r t a) -> !(Prod r t (a -> b)) -> Prod r t b
  Pure :: a -> Prod r t a
  -- Monoid/Alternative. We have to special-case 'many' (though it can be done
  -- with rules) to be able to satisfy the Alternative interface.
  Alts :: ![Prod r t a] -> !(Prod r t (a -> b)) -> Prod r t b
  Many :: !(Prod r t a) -> !(Prod r t ([a] -> b)) -> Prod r t b
  -- Error reporting.
  Named :: !(Prod r t a) -> !Text -> Prod r t a

-- | Match a token for which the given predicate returns @Just a@, and return the @a@.
terminal :: (t -> Maybe a) -> Prod r t a
terminal p = Terminal p (Pure id)

nonTerminal :: r t a -> Prod r t a
nonTerminal p = NonTerminal p (Pure id)

-- | A named production (used for reporting expected things).
(<?>) :: Prod r t a -> Text -> Prod r t a
(<?>) = Named

-- | Lifted instance: @(<>) = 'liftA2' ('<>')@
instance (Semigroup a) => Semigroup (Prod r t a) where
  (<>) = liftA2 (Data.Semigroup.<>)

-- | Lifted instance: @mempty = 'pure' 'mempty'@
instance (Monoid a) => Monoid (Prod r t a) where
  mempty = pure mempty
  mappend = (<>)

instance Functor (Prod r t) where
  {-# INLINE fmap #-}
  fmap f = \case
    Terminal b p -> Terminal b $ fmap (f .) p
    NonTerminal r p -> NonTerminal r $ fmap (f .) p
    Pure x -> Pure $ f x
    Alts as p -> Alts as $ fmap (f .) p
    Many p q -> Many p $ fmap (f .) q
    Named p n -> Named (fmap f p) n

-- | Smart constructor for alternatives.
alts :: [Prod r t a] -> Prod r t (a -> b) -> Prod r t b
alts as p =
  case as >>= go of
    [] -> empty
    [a] -> a <**> p
    as' -> Alts as' p
  where
    go = \case
      Alts [] _ -> []
      Alts as' (Pure f) -> fmap f <$> as'
      Named p' n -> map (<?> n) $ go p'
      a -> [a]

instance Applicative (Prod r t) where
  pure = Pure

  Terminal b p <*> q = Terminal b $ flip <$> p <*> q
  NonTerminal r p <*> q = NonTerminal r $ flip <$> p <*> q
  Pure f <*> q = fmap f q
  Alts as p <*> q = alts as $ flip <$> p <*> q
  Many a p <*> q = Many a $ flip <$> p <*> q
  Named p n <*> q = Named (p <*> q) n
  {-# INLINE (<*>) #-}

instance Alternative (Prod r t) where
  empty = Alts [] $ Pure id

  Named p m <|> q = Named (p <|> q) m
  p <|> Named q n = Named (p <|> q) n
  p <|> q = alts [p, q] $ Pure id

  many (Alts [] _) = Pure []
  many p = Many p $ Pure id

  some p = (:) <$> p <*> many p

-- | String literals can be interpreted as 'Terminal's
-- that match that string.
--
-- >>> :set -XOverloadedStrings
-- >>> import Data.Text (Text)
-- >>> let determiner = "the" <|> "a" <|> "an" :: Prod r e Text Text
instance (IsString t, Eq t, a ~ t) => IsString (Prod r t a) where
  fromString s = Terminal f $ Pure id
    where
      fs = fromString s
      f t | t == fs = Just fs
      f _ = Nothing
  {-# INLINE fromString #-}

-- | A context-free grammar.
--
-- The type parameters are:
--
-- @a@: The return type of the grammar (often a 'Prod').
--
-- @r@ for rule: The type of a non-terminal. This plays a role similar to the
-- @s@ in the type @ST s a@.  Since the 'parser' function expects the @r@ to be
-- universally quantified, there is not much to do with this parameter other
-- than leaving it universally quantified.
--
-- Most of the functionality of 'Grammar's is obtained through its instances,
-- e.g.  'Monad' and 'MonadFix'. Note that GHC has syntactic sugar for
-- 'MonadFix': use @{-\# LANGUAGE RecursiveDo \#-}@ and @mdo@ instead of
-- @do@.
data Grammar r a where
  RuleBind :: Prod r t a -> (Prod r t a -> Grammar r b) -> Grammar r b
  FixBind :: (a -> Grammar r a) -> (a -> Grammar r b) -> Grammar r b
  Return :: a -> Grammar r a

instance Functor (Grammar r) where
  fmap f = \case
    RuleBind ps h -> RuleBind ps (fmap f . h)
    FixBind g h -> FixBind g (fmap f . h)
    Return x -> Return $ f x

instance Applicative (Grammar r) where
  pure = Return
  (<*>) = ap

instance Monad (Grammar r) where
  RuleBind ps f >>= k = RuleBind ps (f >=> k)
  FixBind f g >>= k = FixBind f (g >=> k)
  Return x >>= k = k x

instance MonadFix (Grammar r) where
  mfix f = FixBind f pure

-- | Create a new non-terminal by giving its production.
rule :: Prod r t a -> Grammar r (Prod r t a)
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
