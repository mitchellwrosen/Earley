-- | This module exposes the internals of the package: its API may change
-- independently of the PVP-compliant version number.
module Text.Earley.Parser.Internal where

import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Monad.ST
import Data.ListLike (ListLike)
import qualified Data.ListLike as ListLike
import Data.STRef
import Data.Text (Text)
import Text.Earley.Grammar

-------------------------------------------------------------------------------

-- * Concrete rules and productions

-------------------------------------------------------------------------------

-- | The concrete rule type that the parser uses
data Rule s r t a = Rule
  { ruleProd :: ProdR s r t a,
    ruleConts :: !(STRef s (STRef s [Cont s r t a r])),
    ruleNulls :: !(Results s a)
  }

mkRule :: ProdR s r t a -> ST s (Rule s r t a)
mkRule p = mdo
  c <- newSTRef =<< newSTRef mempty
  computeNullsRef <- newSTRef $ do
    writeSTRef computeNullsRef $ return []
    ns <- unResults $ prodNulls p
    writeSTRef computeNullsRef $ return ns
    return ns
  return $ Rule (removeNulls p) c (Results $ join $ readSTRef computeNullsRef)

prodNulls :: ProdR s r t a -> Results s a
prodNulls prod = case prod of
  Terminal {} -> empty
  NonTerminal r p -> ruleNulls r <**> prodNulls p
  Pure a -> pure a
  Alts as p -> mconcat (map prodNulls as) <**> prodNulls p
  Many a p -> prodNulls (pure [] <|> pure <$> a) <**> prodNulls p
  Named p _ -> prodNulls p

-- | Remove (some) nulls from a production
removeNulls :: ProdR s r t a -> ProdR s r t a
removeNulls prod = case prod of
  Terminal {} -> prod
  NonTerminal {} -> prod
  Pure _ -> empty
  Alts as (Pure f) -> alts (map removeNulls as) $ Pure f
  Alts {} -> prod
  Many {} -> prod
  Named p n -> Named (removeNulls p) n

type ProdR s r t a = Prod (Rule s r) t a

resetConts :: Rule s r t a -> ST s ()
resetConts r = writeSTRef (ruleConts r) =<< newSTRef mempty

-------------------------------------------------------------------------------

-- * Delayed results

-------------------------------------------------------------------------------
newtype Results s a = Results {unResults :: ST s [a]}
  deriving (Functor)

lazyResults :: ST s [a] -> ST s (Results s a)
lazyResults stas = mdo
  resultsRef <- newSTRef $ do
    as <- stas
    writeSTRef resultsRef $ return as
    return as
  return $ Results $ join $ readSTRef resultsRef

instance Applicative (Results s) where
  pure = Results . pure . pure
  (<*>) = ap

instance Alternative (Results s) where
  empty = Results $ pure []
  Results sxs <|> Results sys = Results $ (<|>) <$> sxs <*> sys

instance Monad (Results s) where
  return = pure
  Results stxs >>= f = Results $ do
    xs <- stxs
    concat <$> mapM (unResults . f) xs

instance Semigroup (Results s a) where
  (<>) = (<|>)

instance Monoid (Results s a) where
  mempty = empty
  mappend = (<>)

-------------------------------------------------------------------------------

-- * States and continuations

-------------------------------------------------------------------------------
data BirthPos
  = Previous
  | Current
  deriving (Eq)

-- | An Earley state with result type @a@.
data State s r t a where
  State ::
    !(ProdR s r t a) ->
    !(a -> Results s b) ->
    !BirthPos ->
    !(Conts s r t b c) ->
    State s r t c
  Final :: !(Results s a) -> State s r t a

-- | A continuation accepting an @a@ and producing a @b@.
data Cont s r t a b where
  Cont ::
    !(a -> Results s b) ->
    !(ProdR s r t (b -> c)) ->
    !(c -> Results s d) ->
    !(Conts s r t d e') ->
    Cont s r t a e'
  FinalCont :: (a -> Results s c) -> Cont s r t a c

data Conts s r t a c = Conts
  { conts :: !(STRef s [Cont s r t a c]),
    contsArgs :: !(STRef s (Maybe (STRef s (Results s a))))
  }

newConts :: STRef s [Cont s r t a c] -> ST s (Conts s r t a c)
newConts r = Conts r <$> newSTRef Nothing

contraMapCont :: (b -> Results s a) -> Cont s r t a c -> Cont s r t b c
contraMapCont f (Cont g p args cs) = Cont (f >=> g) p args cs
contraMapCont f (FinalCont args) = FinalCont (f >=> args)

contToState :: BirthPos -> Results s a -> Cont s r t a c -> State s r t c
contToState pos r (Cont g p args cs) = State p (\f -> r >>= g >>= args . f) pos cs
contToState _ r (FinalCont args) = Final $ r >>= args

-- | Strings of non-ambiguous continuations can be optimised by removing
-- indirections.
simplifyCont :: Conts s r t b a -> ST s [Cont s r t b a]
simplifyCont Conts {conts = cont} = readSTRef cont >>= go False
  where
    go !_ [Cont g (Pure f) args cont'] = do
      ks' <- simplifyCont cont'
      go True $ map (contraMapCont $ g >=> args . f) ks'
    go True ks = do
      writeSTRef cont ks
      return ks
    go False ks = return ks

-------------------------------------------------------------------------------

-- * Grammars

-------------------------------------------------------------------------------

-- | Given a grammar, construct an initial state.
initialState :: ProdR s a t a -> ST s (State s a t a)
initialState p = State p pure Previous <$> (newConts =<< newSTRef [FinalCont pure])

-------------------------------------------------------------------------------

-- * Parsing

-------------------------------------------------------------------------------

-- | A parsing report, which contains fields that are useful for presenting
-- errors to the user if a parse is deemed a failure.  Note however that we get
-- a report even when we successfully parse something.
data Report i = Report
  { -- | The final position in the input (0-based) that the
    -- parser reached.
    position :: Int,
    -- | The named productions processed at the final
    -- position.
    expected :: [Text],
    -- | The part of the input string that was not consumed,
    -- which may be empty.
    unconsumed :: i
  }
  deriving (Eq, Ord, Read, Show)

-- | The result of a parse.
data Result s i a
  = -- | The parser ended.
    Ended (Report i)
  | -- | The parser parsed a number of @a@s.  These are given as a computation,
    -- @'ST' s [a]@ that constructs the 'a's when run.  We can thus save some
    -- work by ignoring this computation if we do not care about the results.
    -- The 'Int' is the position in the input where these results were
    -- obtained, the @i@ the rest of the input, and the last component is the
    -- continuation.
    Parsed (ST s [a]) Int i (ST s (Result s i a))
  deriving (Functor)

data ParseEnv s i t a = ParseEnv
  { -- | Results ready to be reported (when this position has been processed)
    results :: ![ST s [a]],
    -- | States to process at the next position
    next :: ![State s a t a],
    -- | Computation that resets the continuation refs of productions
    reset :: !(ST s ()),
    -- | Named productions encountered at this position
    names :: ![Text],
    -- | The current position in the input string
    curPos :: !Int,
    -- | The input string
    input :: !i
  }

{-# INLINE emptyParseEnv #-}
emptyParseEnv :: i -> ParseEnv s i t a
emptyParseEnv i =
  ParseEnv
    { results = mempty,
      next = mempty,
      reset = return (),
      names = mempty,
      curPos = 0,
      input = i
    }

{-# SPECIALIZE parse ::
  [State s a t a] ->
  ParseEnv s [t] t a ->
  ST s (Result s [t] a)
  #-}

-- | The internal parsing routine
parse ::
  (ListLike i t) =>
  -- | States to process at this position
  [State s a t a] ->
  ParseEnv s i t a ->
  ST s (Result s i a)
parse [] env@ParseEnv {results = [], next = []} = do
  reset env
  return $
    Ended
      Report
        { position = curPos env,
          expected = names env,
          unconsumed = input env
        }
parse [] env@ParseEnv {results = []} = do
  reset env
  parse
    (next env)
    (emptyParseEnv $ ListLike.drop 1 $ input env) {curPos = curPos env + 1}
parse [] env = do
  reset env
  return $
    Parsed (concat <$> sequence (results env)) (curPos env) (input env) $
      parse [] env {results = [], reset = return ()}
parse (st : ss) env = case st of
  Final res -> parse ss env {results = unResults res : results env}
  State pr args pos scont -> case pr of
    Terminal f p -> case ListLike.uncons (input env) >>= f . fst of
      Just a ->
        parse
          ss
          env
            { next =
                State p (args . ($ a)) Previous scont
                  : next env
            }
      Nothing -> parse ss env
    NonTerminal r p -> do
      rkref <- readSTRef $ ruleConts r
      ks <- readSTRef rkref
      writeSTRef rkref (Cont pure p args scont : ks)
      ns <- unResults $ ruleNulls r
      let addNullState
            | null ns = id
            | otherwise =
                (:) $
                  State p (\f -> Results (pure $ map f ns) >>= args) pos scont
      if null ks
        then do
          -- The rule has not been expanded at this position.
          st' <- State (ruleProd r) pure Current <$> newConts rkref
          parse
            (addNullState $ st' : ss)
            env {reset = resetConts r >> reset env}
        else -- The rule has already been expanded at this position.
          parse (addNullState ss) env
    Pure a
      -- Skip following continuations that stem from the current position; such
      -- continuations are handled separately.
      | pos == Current -> parse ss env
      | otherwise -> do
          let argsRef = contsArgs scont
          masref <- readSTRef argsRef
          case masref of
            Just asref -> do
              -- The continuation has already been followed at this position.
              modifySTRef asref $ mappend $ args a
              parse ss env
            Nothing -> do
              -- It hasn't.
              asref <- newSTRef $ args a
              writeSTRef argsRef $ Just asref
              ks <- simplifyCont scont
              res <- lazyResults $ unResults =<< readSTRef asref
              let kstates = map (contToState pos res) ks
              parse
                (kstates ++ ss)
                env {reset = writeSTRef argsRef Nothing >> reset env}
    Alts as (Pure f) -> do
      let args' = args . f
          sts = [State a args' pos scont | a <- as]
      parse (sts ++ ss) env
    Alts as p -> do
      scont' <- newConts =<< newSTRef [Cont pure p args scont]
      let sts = [State a pure Previous scont' | a <- as]
      parse (sts ++ ss) env
    Many p q -> mdo
      r <- mkRule $ pure [] <|> (:) <$> p <*> NonTerminal r (Pure id)
      parse (State (NonTerminal r q) args pos scont : ss) env
    Named pr' n ->
      parse
        (State pr' args pos scont : ss)
        env {names = n : names env}

type Parser i a = forall s. i -> ST s (Result s i a)

{-# INLINE parser #-}

-- | Create a parser from the given grammar.
parser ::
  (ListLike i t) =>
  (forall r. Grammar r (Prod r t a)) ->
  Parser i a
parser g i = do
  let nt x = NonTerminal x $ pure id
  s <- initialState =<< runGrammar (fmap nt . mkRule) g
  parse [s] $ emptyParseEnv i

-- | Return all parses from the result of a given parser. The result may
-- contain partial parses. The 'Int's are the position at which a result was
-- produced.
--
-- The elements of the returned list of results are sorted by their position in
-- ascending order.  If there are multiple results at the same position they
-- are returned in an unspecified order.
allParses ::
  Parser i a ->
  i ->
  ([(a, Int)], Report i)
allParses p i = runST $ p i >>= go
  where
    go :: Result s i a -> ST s ([(a, Int)], Report i)
    go r = case r of
      Ended rep -> return ([], rep)
      Parsed mas cpos _ k -> do
        as <- mas
        fmap (first (map (,cpos) as ++)) $ go =<< k

{-# INLINE fullParses #-}

-- | Return all parses that reached the end of the input from the result of a
-- given parser.
--
-- If there are multiple results they are returned in an unspecified order.
fullParses ::
  (ListLike i t) =>
  Parser i a ->
  i ->
  ([a], Report i)
fullParses p i = runST $ p i >>= go
  where
    go :: (ListLike i t) => Result s i a -> ST s ([a], Report i)
    go r = case r of
      Ended rep -> return ([], rep)
      Parsed mas _ i' k
        | ListLike.null i' -> do
            as <- mas
            fmap (first (as ++)) $ go =<< k
        | otherwise -> go =<< k

{-# INLINE report #-}

-- | See e.g. how far the parser is able to parse the input string before it
-- fails.  This can be much faster than getting the parse results for highly
-- ambiguous grammars.
report ::
  Parser i a ->
  i ->
  Report i
report p i = runST $ p i >>= go
  where
    go :: Result s i a -> ST s (Report i)
    go r = case r of
      Ended rep -> return rep
      Parsed _ _ _ k -> go =<< k
