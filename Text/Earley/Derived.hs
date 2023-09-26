-- | Derived operators.
module Text.Earley.Derived where

import Control.Monad (guard)
import Text.Earley.Grammar
import Text.Earley.Parser

-- | Match a token that satisfies the given predicate. Returns the matched
-- token. See also 'terminal'.
satisfy :: (a -> Bool) -> Prod r a a
satisfy p = terminal ((<$) <*> guard . p)
{-# INLINE satisfy #-}

-- | Match a single token.
token :: (Eq a) => a -> Prod r a a
token x = satisfy (== x)

-- | Match a single token with any value
anyToken :: Prod r a a
anyToken = terminal Just

-- | Match a list of tokens in sequence.
list :: (Eq a) => [a] -> Prod r a [a]
list = foldr ((\x y -> (:) <$> x <*> y) . satisfy . (==)) (pure [])
{-# INLINE list #-}

-- | Whether or not the grammar matches the input string. Equivalently,
-- whether the given input is in the language described by the grammars.
matches :: (forall r. Grammar r (Prod r t a)) -> [t] -> Bool
matches grammar = not . null . fst . fullParses (parser grammar)
