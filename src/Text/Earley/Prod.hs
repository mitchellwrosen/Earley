module Text.Earley.Prod
  ( Prod (..),
    terminal,
    nonTerminal,
    (<?>),
    alts,
  )
where

import Control.Applicative
import Data.Text (Text)

-- | A @Prod s t a@ is a production of tokens @t@ with result type @a@.
data Prod s t a where
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

instance Functor (Prod r t) where
  fmap f = \case
    Terminal b p -> Terminal b $ fmap (f .) p
    NonTerminal r p -> NonTerminal r $ fmap (f .) p
    Pure x -> Pure $ f x
    Alts as p -> Alts as $ fmap (f .) p
    Many p q -> Many p $ fmap (f .) q
    Named p n -> Named (fmap f p) n
  {-# INLINE fmap #-}

instance (Monoid a) => Monoid (Prod s t a) where
  mempty = pure mempty

instance (Semigroup a) => Semigroup (Prod s t a) where
  (<>) = liftA2 (<>)

-- | Match a token for which the given predicate returns @Just a@, and return the @a@.
terminal :: (t -> Maybe a) -> Prod s t a
terminal p = Terminal p (Pure id)

nonTerminal :: r t a -> Prod r t a
nonTerminal p = NonTerminal p (Pure id)

-- | A named production (used for reporting expected things).
(<?>) :: Prod s t a -> Text -> Prod s t a
(<?>) = Named

infixr 0 <?>

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
