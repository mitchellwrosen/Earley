-- | Derived operators.
module Text.Earley.Derived where

import Control.Monad (guard)
import Data.ListLike (ListLike)
import qualified Data.ListLike as ListLike
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
list = listLike

-- | Match a 'ListLike' of tokens in sequence.
{-# INLINE listLike #-}
listLike :: (Eq t, ListLike i t) => i -> Prod r t i
listLike = ListLike.foldr ((\x y -> ListLike.cons <$> x <*> y) . satisfy . (==)) (pure ListLike.empty)

-- | Whether or not the grammar matches the input string. Equivalently,
-- whether the given input is in the language described by the grammars.
matches :: (ListLike i t) => (forall r. Grammar r (Prod r t a)) -> i -> Bool
matches grammar = not . null . fst . fullParses (parser grammar)
