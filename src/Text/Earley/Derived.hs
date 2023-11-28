-- | Derived operators.
module Text.Earley.Derived where

import Control.Monad (guard)
import Text.Earley.Grammar
import Text.Earley.Parser

-- | Match a token that satisfies the given predicate. Returns the matched
-- token. See also 'terminal'.
{-# INLINE satisfy #-}
satisfy :: (t -> Bool) -> Prod r t t
satisfy p = terminal ((<$) <*> guard . p)

-- | Match a single token.
token :: (Eq t) => t -> Prod r t t
token x = satisfy (== x)

-- | Match a single token with any value
anyToken :: Prod r t t
anyToken = terminal Just

-- | Match a list of tokens in sequence.
{-# INLINE list #-}
list :: (Eq t) => [t] -> Prod r t [t]
list = foldr ((\x y -> (:) <$> x <*> y) . satisfy . (==)) (pure [])

-- | Whether or not the grammar matches the input string. Equivalently,
-- whether the given input is in the language described by the grammars.
matches :: (forall r. Grammar r (Prod r t a)) -> [t] -> Bool
matches grammar = not . null . fst . fullParses (parser grammar)
