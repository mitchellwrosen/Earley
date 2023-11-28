-- | This module exposes the internals of the package: its API may change
-- independently of the PVP-compliant version number.
module Text.Earley.Parser.Internal
  ( Parser,
    Report (..),
    Result (..),
    allParses,
    fullParses,
    parser,
    report,
  )
where

import Control.Applicative
import Control.Monad
import Control.Monad.ST
import Data.Function ((&))
import Data.STRef
import Data.Text (Text)
import Text.Earley.Grammar (Grammar)
import Text.Earley.Grammar qualified as Grammar
import Text.Earley.Prod (Prod)
import Text.Earley.Prod qualified as Prod

-------------------------------------------------------------------------------
-- Concrete rules and productions
-------------------------------------------------------------------------------

-- | The concrete rule type that the parser uses
data Rule s r t a = Rule
  { prod :: ProdR s r t a,
    conts :: !(STRef s (STRef s [Cont s r t a r])),
    nulls :: !(Results s a)
  }

mkRule :: ProdR s r t a -> ST s (Rule s r t a)
mkRule p = mdo
  c <- newSTRef =<< newSTRef mempty
  computeNullsRef <-
    newSTRef do
      writeSTRef computeNullsRef (pure [])
      ns <- runResults (prodNulls p)
      writeSTRef computeNullsRef $ pure ns
      pure ns
  pure
    Rule
      { prod = removeNulls p,
        conts = c,
        nulls = Results $ join $ readSTRef computeNullsRef
      }

prodNulls :: ProdR s r t a -> Results s a
prodNulls = \case
  Prod.Terminal {} -> mempty
  Prod.NonTerminal r p -> r.nulls <**> prodNulls p
  Prod.Pure a -> pure a
  Prod.Alts as p -> foldMap prodNulls as <**> prodNulls p
  Prod.Many a p -> prodNulls (pure [] <|> pure <$> a) <**> prodNulls p
  Prod.Named p _ -> prodNulls p

-- | Remove (some) nulls from a production
removeNulls :: ProdR s r t a -> ProdR s r t a
removeNulls prod = case prod of
  Prod.Terminal {} -> prod
  Prod.NonTerminal {} -> prod
  Prod.Pure _ -> empty
  Prod.Alts as (Prod.Pure f) -> Prod.alts (map removeNulls as) $ Prod.Pure f
  Prod.Alts {} -> prod
  Prod.Many {} -> prod
  Prod.Named p n -> Prod.Named (removeNulls p) n

type ProdR s r t a = Prod (Rule s r) t a

-------------------------------------------------------------------------------
-- Delayed results
-------------------------------------------------------------------------------

newtype Results s a
  = Results (ST s [a])
  deriving (Functor)

instance Applicative (Results s) where
  pure x = Results (pure [x])
  (<*>) = ap

instance Monad (Results s) where
  Results mx >>= f =
    Results do
      xs <- mx
      concat <$> traverse (runResults . f) xs

instance Monoid (Results s a) where
  mempty = Results (pure [])

instance Semigroup (Results s a) where
  Results xs <> Results ys = Results ((++) <$> xs <*> ys)

runResults :: Results s a -> ST s [a]
runResults (Results m) = m

cacheResultsRef :: STRef s (Results s a) -> ST s (Results s a)
cacheResultsRef ref = do
  xs <-
    cached do
      xs <- readSTRef ref
      runResults xs
  pure (Results xs)

-- Cache an action by returning a new action that:
--
--   * when run for the first time, runs the original action and returns the result
--   * every time thereafter, returns that same result
cached :: ST s a -> ST s (ST s a)
cached action = mdo
  resultRef <-
    newSTRef do
      result <- action
      writeSTRef resultRef (pure result)
      pure result
  pure (join (readSTRef resultRef))

-------------------------------------------------------------------------------
-- States and continuations
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
    !(Conts s r t d e) ->
    Cont s r t a e
  FinalCont :: (a -> Results s b) -> Cont s r t a b

data BeenFollowed s a
  = HasntBeenFollowed
  | HasBeenFollowed !(STRef s (Results s a))

data Conts s r t a b = Conts
  { conts :: !(STRef s [Cont s r t a b]),
    args :: !(STRef s (BeenFollowed s a))
  }

newConts :: STRef s [Cont s r t a c] -> ST s (Conts s r t a c)
newConts r = Conts r <$> newSTRef HasntBeenFollowed

contraMapCont :: (b -> Results s a) -> Cont s r t a c -> Cont s r t b c
contraMapCont f = \case
  Cont g p args cs -> Cont (f >=> g) p args cs
  FinalCont args -> FinalCont (f >=> args)

contToState :: Results s a -> Cont s r t a c -> State s r t c
contToState r = \case
  Cont g p args cs -> State p (\f -> r >>= g >>= args . f) Previous cs
  FinalCont args -> Final (r >>= args)

-- | Strings of non-ambiguous continuations can be optimised by removing
-- indirections.
simplifyCont :: Conts s r t b a -> ST s [Cont s r t b a]
simplifyCont Conts {conts = cont} = readSTRef cont >>= go False
  where
    go !_ [Cont g (Prod.Pure f) args cont'] = do
      ks' <- simplifyCont cont'
      go True $ map (contraMapCont $ g >=> args . f) ks'
    go True ks = do
      writeSTRef cont ks
      return ks
    go False ks = return ks

-------------------------------------------------------------------------------
-- Grammars
-------------------------------------------------------------------------------

-- | Given a grammar, construct an initial state.
initialState :: ProdR s a t a -> ST s (State s a t a)
initialState p = State p pure Previous <$> (newConts =<< newSTRef [FinalCont pure])

-------------------------------------------------------------------------------
-- Parsing
-------------------------------------------------------------------------------

-- | A parsing report, which contains fields that are useful for presenting
-- errors to the user if a parse is deemed a failure.  Note however that we get
-- a report even when we successfully parse something.
data Report t = Report
  { -- | The final position in the input (0-based) that the parser reached.
    position :: Int,
    -- | The named productions processed at the final position.
    expected :: [Text],
    -- | The part of the input string that was not consumed,
    -- which may be empty.
    unconsumed :: [t]
  }
  deriving (Eq, Ord, Read, Show)

-- | The result of a parse.
data Result s t a
  = -- | The parser ended.
    Ended (Report t)
  | -- | The parser parsed a number of @a@s.
    Parsed
      -- These are given as a computation, @'ST' s [a]@ that constructs the 'a's when run.  We can thus save some work
      -- by ignoring this computation if we do not care about the results.
      [Results s a]
      -- The position in the input where these results were obtained.
      Int
      -- The rest of the input.
      [t]
      -- The continuation
      (ST s (Result s t a))
  deriving stock (Functor)

data ParseEnv s t a = ParseEnv
  { -- The input tokens
    tokens :: ![t],
    -- The current offset in the input tokens
    offset :: !Int,
    -- States to process at the current position
    states :: ![State s a t a],
    -- States to process at the next position
    nextStates :: ![State s a t a],
    -- | Results ready to be reported (when this position has been processed)
    results :: ![Results s a],
    -- | Computation that resets the continuation refs of productions
    reset :: !(ST s ()),
    -- | Named productions encountered at this position
    names :: ![Text]
  }

addCurrentState :: State s a t a -> ParseEnv s t a -> ParseEnv s t a
addCurrentState state env =
  env {states = state : env.states}

addCurrentStates :: [State s a t a] -> ParseEnv s t a -> ParseEnv s t a
addCurrentStates states env =
  env {states = states ++ env.states}

addNextState :: State s a t a -> ParseEnv s t a -> ParseEnv s t a
addNextState state env =
  env {nextStates = state : env.nextStates}

addResult :: Results s a -> ParseEnv s t a -> ParseEnv s t a
addResult result env =
  env {results = result : env.results}

-- | The internal parsing routine
parseCurrentStates :: ParseEnv s t a -> ST s (Result s t a)
parseCurrentStates env =
  case env.states of
    [] -> do
      env.reset
      if null env.results
        then keepGoing
        else pure (Parsed env.results env.offset env.tokens keepGoing)
      where
        keepGoing =
          case env.nextStates of
            [] ->
              pure $
                Ended
                  Report
                    { position = env.offset,
                      expected = env.names,
                      unconsumed = env.tokens
                    }
            state : states ->
              parseCurrentState
                ParseEnv
                  { tokens = drop 1 env.tokens,
                    offset = env.offset + 1,
                    states,
                    nextStates = [],
                    results = [],
                    reset = pure (),
                    names = []
                  }
                state
    state : states -> parseCurrentState env {states} state

parseCurrentState :: ParseEnv s t a -> State s a t a -> ST s (Result s t a)
parseCurrentState env = \case
  Final result -> parseCurrentStates (env & addResult result)
  State pr args pos conts ->
    case pr of
      Prod.Terminal f p -> parseCurrentTerminal env args conts f p
      Prod.NonTerminal rule p -> parseCurrentNonterminal env args pos conts rule p
      Prod.Pure x -> parseCurrentPure env pos conts (args x)
      Prod.Alts as (Prod.Pure f) ->
        parseCurrentStates $
          env
            & addCurrentStates [State a (args . f) pos conts | a <- as]
      Prod.Alts as p -> do
        scont' <- newConts =<< newSTRef [Cont pure p args conts]
        parseCurrentStates $
          env
            & addCurrentStates [State a pure Previous scont' | a <- as]
      Prod.Many p q -> mdo
        r <- mkRule $ pure [] <|> (:) <$> p <*> Prod.NonTerminal r (Prod.Pure id)
        parseCurrentStates $
          env
            & addCurrentState (State (Prod.NonTerminal r q) args pos conts)
      Prod.Named pr' n ->
        parseCurrentStates $
          env
            { names = n : names env
            }
            & addCurrentState (State pr' args pos conts)

parseCurrentTerminal ::
  ParseEnv s t a ->
  (b -> Results s c) ->
  Conts s a t c a ->
  (t -> Maybe d) ->
  ProdR s a t (d -> b) ->
  ST s (Result s t a)
parseCurrentTerminal env args scont f p =
  parseCurrentStates $
    case maybeValue of
      Nothing -> env
      Just value -> env & addNextState (State p (\x -> args (x value)) Previous scont)
  where
    maybeValue =
      case tokens env of
        [] -> Nothing
        token : _ -> f token

parseCurrentNonterminal ::
  ParseEnv s t a ->
  (b -> Results s c) ->
  BirthPos ->
  Conts s a t c a ->
  Rule s a t d ->
  ProdR s a t (d -> b) ->
  ST s (Result s t a)
parseCurrentNonterminal env args pos scont rule p = do
  rkref <- readSTRef rule.conts
  ks <- readSTRef rkref
  writeSTRef rkref (Cont pure p args scont : ks)
  ns <- runResults rule.nulls
  env1 <-
    case null ks of
      -- The rule has not been expanded at this position.
      True -> do
        st' <- State rule.prod pure Current <$> newConts rkref
        pure $
          env
            { reset = do
                writeSTRef rule.conts =<< newSTRef []
                env.reset
            }
            & addCurrentState st'
      -- The rule has already been expanded at this position.
      False -> pure env
  parseCurrentStates
    if null ns
      then env1
      else env1 & addCurrentState (State p (\f -> Results (pure $ map f ns) >>= args) pos scont)

parseCurrentPure ::
  ParseEnv s t a ->
  BirthPos ->
  Conts s a t b a ->
  (Results s b) ->
  ST s (Result s t a)
parseCurrentPure env pos conts x =
  case pos of
    -- Skip following continuations that stem from the current position; such
    -- continuations are handled separately.
    Current -> parseCurrentStates env
    Previous -> do
      readSTRef conts.args >>= \case
        HasBeenFollowed asref -> do
          -- The continuation has already been followed at this position.
          modifySTRef asref (x <>)
          parseCurrentStates env
        HasntBeenFollowed -> do
          -- It hasn't.
          asref <- newSTRef x
          writeSTRef conts.args $ HasBeenFollowed asref
          ks <- simplifyCont conts
          res <- cacheResultsRef asref
          parseCurrentStates $
            env
              { reset = do
                  writeSTRef conts.args HasntBeenFollowed
                  env.reset
              }
              & addCurrentStates (map (contToState res) ks)

newtype Parser t a = Parser (forall s. [t] -> ST s (Result s t a))

-- | Create a parser from the given grammar.
parser :: (forall r. Grammar r (Prod r t a)) -> Parser t a
parser g =
  Parser \i -> do
    s <- initialState =<< Grammar.runGrammar (fmap Prod.nonTerminal . mkRule) g
    parseCurrentState
      ParseEnv
        { tokens = i,
          offset = 0,
          states = [],
          nextStates = [],
          results = [],
          reset = pure (),
          names = []
        }
      s
{-# INLINE parser #-}

-- | Return all parses from the result of a given parser. The result may
-- contain partial parses. The 'Int's are the position at which a result was
-- produced.
--
-- The elements of the returned list of results are sorted by their position in
-- ascending order.  If there are multiple results at the same position they
-- are returned in an unspecified order.
allParses :: Parser t a -> [t] -> ([(a, Int)], Report t)
allParses (Parser p) i = runST (p i >>= go)
  where
    go :: Result s t a -> ST s ([(a, Int)], Report t)
    go = \case
      Ended rep -> pure ([], rep)
      Parsed mas cpos _ k -> do
        as <- traverse runResults mas
        (bs, rep) <- go =<< k
        pure (map (,cpos) (concat as) ++ bs, rep)

-- | Return all parses that reached the end of the input from the result of a
-- given parser.
--
-- If there are multiple results they are returned in an unspecified order.
fullParses :: Parser t a -> [t] -> ([a], Report t)
fullParses (Parser p) i = runST (p i >>= go)
  where
    go :: Result s t a -> ST s ([a], Report t)
    go = \case
      Ended rep -> pure ([], rep)
      Parsed mas _ i' k
        | null i' -> do
            as <- traverse runResults mas
            (bs, rep) <- go =<< k
            pure (concat as ++ bs, rep)
        | otherwise -> go =<< k
{-# INLINE fullParses #-}

-- | See e.g. how far the parser is able to parse the input string before it
-- fails.  This can be much faster than getting the parse results for highly
-- ambiguous grammars.
report :: Parser t a -> [t] -> Report t
report (Parser p) i = runST (p i >>= go)
  where
    go :: Result s i a -> ST s (Report i)
    go = \case
      Ended rep -> pure rep
      Parsed _ _ _ k -> go =<< k
{-# INLINE report #-}
