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
    contsRefRef :: !(STRef s (ContsRef s r t a r)),
    nulls :: !(Results s a)
  }

mkRule :: ProdR s r t a -> ST s (Rule s r t a)
mkRule p = mdo
  contsRefRef <- newSTRef =<< newSTRef []
  computeNullsRef <-
    newSTRef do
      writeSTRef computeNullsRef (pure [])
      ns <- runResults (prodNulls p)
      writeSTRef computeNullsRef $ pure ns
      pure ns
  pure
    Rule
      { prod = removeNulls p,
        contsRefRef,
        nulls = Results $ join $ readSTRef computeNullsRef
      }

resetRuleConts :: Rule s r t a -> ST s ()
resetRuleConts rule = do
  ref <- newSTRef []
  writeSTRef rule.contsRefRef ref

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
  State :: !(State1 s r t x y a) -> State s r t a
  Final :: !(Results s a) -> State s r t a

data State1 s r t a b c = State1
  { prod :: !(ProdR s r t a),
    args :: !(K s a b),
    pos :: !BirthPos,
    conts :: !(Conts s r t b c)
  }

-- | A continuation accepting an @a@ and producing a list of @b@.
data Cont s r t a b where
  Cont ::
    !(K s a α) ->
    !(ProdR s r t (α -> β)) ->
    !(K s β γ) ->
    !(Conts s r t γ b) ->
    Cont s r t a b
  FinalCont :: K s a b -> Cont s r t a b

newtype K s a b
  = K (a -> Results s b)

(>*>) :: K s a b -> K s b c -> K s a c
K f >*> K g = K (f >=> g)

runK :: K s a b -> a -> Results s b
runK (K f) = f

manyK :: K s a b -> K s (Results s a) b
manyK (K f) = K (>>= f)

idK :: K s a a
idK = K pure

lmapK :: (b -> a) -> K s a c -> K s b c
lmapK f (K g) = K (g . f)

-- rmapK :: (b -> c) -> K s a b -> K s a c
-- rmapK f (K g) = K (fmap f . g)

pureK :: (a -> [b]) -> K s a b
pureK f = K (Results . pure . f)

data BeenFollowed s a
  = HasntBeenFollowed
  | HasBeenFollowed !(STRef s (Results s a))

data Conts s r t a b = Conts
  { contsRef :: !(ContsRef s r t a b),
    args :: !(STRef s (BeenFollowed s a))
  }

type ContsRef s r t a b =
  STRef s [Cont s r t a b]

newConts :: ContsRef s r t a b -> ST s (Conts s r t a b)
newConts contsRef = do
  args <- newSTRef HasntBeenFollowed
  pure Conts {contsRef, args}

contraMapCont :: K s b a -> Cont s r t a c -> Cont s r t b c
contraMapCont f = \case
  Cont g p args cs -> Cont (f >*> g) p args cs
  FinalCont args -> FinalCont (f >*> args)

contToState :: Results s a -> Cont s r t a b -> State s r t b
contToState res = \case
  Cont
    (g :: K s a α)
    (prod :: ProdR s r t (α -> β))
    (args :: K s β γ)
    (conts :: Conts s r t γ b) ->
      State
        State1
          { prod,
            args = K (\f -> run (manyK g >*> lmapK f args)),
            pos = Previous,
            conts
          }
  FinalCont args -> Final (run (manyK args))
  where
    run k = runK k res

-- | Strings of non-ambiguous continuations can be optimised by removing indirections.
simplifyCont :: Conts s r t a b -> ST s [Cont s r t a b]
simplifyCont conts = do
  ks <- readSTRef conts.contsRef
  go False ks
  where
    go changed = \case
      [Cont g (Prod.Pure f) args cont'] -> do
        ks' <- simplifyCont cont'
        go True (map (contraMapCont $ g >*> lmapK f args) ks')
      ks -> do
        when changed (writeSTRef conts.contsRef ks)
        pure ks

-------------------------------------------------------------------------------
-- Grammars
-------------------------------------------------------------------------------

-- | Given a production, construct an initial state.
initialState :: ProdR s a t a -> ST s (State s a t a)
initialState prod = do
  conts <- newConts =<< newSTRef [FinalCont idK]
  pure $
    State
      State1
        { prod,
          args = idK,
          pos = Previous,
          conts
        }

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
    -- | Named productions encountered at this position
    names :: ![Text],
    -- States to process at the current position
    states :: ![State s a t a],
    -- States to process at the next position
    nextStates :: ![State s a t a],
    -- | Results ready to be reported (when this position has been processed)
    results :: ![Results s a],
    -- | Computation that resets the continuation refs of productions
    reset :: !(ST s ())
  }

addName :: Text -> ParseEnv s t a -> ParseEnv s t a
addName name env =
  env {names = name : env.names}

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

addReset :: ST s () -> ParseEnv s t a -> ParseEnv s t a
addReset action env =
  env {reset = env.reset >> action}

-- | The internal parsing routine
parseCurrentStates :: ParseEnv s t a -> ST s (Result s t a)
parseCurrentStates env =
  case env.states of
    [] ->
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
            state : states -> do
              env.reset
              parseCurrentState
                ParseEnv
                  { tokens = drop 1 env.tokens,
                    offset = env.offset + 1,
                    names = [],
                    states,
                    nextStates = [],
                    results = [],
                    reset = pure ()
                  }
                state
    state : states -> parseCurrentState env {states} state

parseCurrentState :: ParseEnv s t a -> State s a t a -> ST s (Result s t a)
parseCurrentState env = \case
  Final result -> parseCurrentStates (env & addResult result)
  State State1 {prod, args, pos, conts} ->
    case prod of
      Prod.Terminal f p -> parseCurrentTerminal env f p args conts
      Prod.NonTerminal rule p -> parseCurrentNonterminal env rule p args pos conts
      Prod.Pure x -> parseCurrentPure env pos (runK args x) conts
      Prod.Alts prods (Prod.Pure f) -> do
        let args' = lmapK f args
        parseCurrentStates $
          env
            & addCurrentStates
              [ State
                  State1
                    { prod = p,
                      args = args',
                      pos,
                      conts
                    }
                | p <- prods
              ]
      Prod.Alts prods prod1 -> do
        conts' <- newConts =<< newSTRef [Cont idK prod1 args conts]
        parseCurrentStates $
          env
            & addCurrentStates
              [ State
                  State1
                    { prod = p,
                      args = idK,
                      pos = Previous,
                      conts = conts'
                    }
                | p <- prods
              ]
      Prod.Many p q -> mdo
        r <- mkRule $ pure [] <|> (:) <$> p <*> Prod.NonTerminal r (Prod.Pure id)
        parseCurrentStates $
          env
            & addCurrentState
              ( State
                  State1
                    { prod = Prod.NonTerminal r q,
                      args,
                      pos,
                      conts
                    }
              )
      Prod.Named prod' name ->
        parseCurrentStates $
          env
            & addCurrentState
              ( State
                  State1
                    { prod = prod',
                      args,
                      pos,
                      conts
                    }
              )
            & addName name

parseCurrentTerminal ::
  ParseEnv s t a ->
  (t -> Maybe x) ->
  ProdR s a t (x -> y) ->
  K s y z ->
  Conts s a t z a ->
  ST s (Result s t a)
parseCurrentTerminal env parse prod args conts =
  parseCurrentStates $
    case maybeValue of
      Nothing -> env
      Just value ->
        env
          & addNextState
            ( State
                State1
                  { prod,
                    args = lmapK (\f -> f value) args,
                    pos = Previous,
                    conts
                  }
            )
  where
    maybeValue =
      case tokens env of
        [] -> Nothing
        token : _ -> parse token

parseCurrentNonterminal ::
  ParseEnv s t a ->
  Rule s a t x ->
  ProdR s a t (x -> y) ->
  K s y z ->
  BirthPos ->
  Conts s a t z a ->
  ST s (Result s t a)
parseCurrentNonterminal env rule prod args pos conts = do
  ruleContsRef <- readSTRef rule.contsRefRef
  ruleConts <- readSTRef ruleContsRef
  writeSTRef ruleContsRef (Cont idK prod args conts : ruleConts)
  ns <- runResults rule.nulls
  env1 <-
    case null ruleConts of
      -- The rule has not been expanded at this position.
      True -> do
        conts' <- newConts ruleContsRef
        pure $
          env
            & addCurrentState
              ( State
                  State1
                    { prod = rule.prod,
                      args = idK,
                      pos = Current,
                      conts = conts'
                    }
              )
            & addReset (resetRuleConts rule)
      -- The rule has already been expanded at this position.
      False -> pure env
  parseCurrentStates
    if null ns
      then env1
      else
        env1
          & addCurrentState
            ( State
                State1
                  { prod,
                    args = pureK (\f -> map f ns) >*> args,
                    pos,
                    conts
                  }
            )

parseCurrentPure ::
  ParseEnv s t a ->
  BirthPos ->
  Results s x ->
  Conts s a t x a ->
  ST s (Result s t a)
parseCurrentPure env pos xs conts =
  case pos of
    -- Skip following continuations that stem from the current position; such
    -- continuations are handled separately.
    Current -> parseCurrentStates env
    Previous -> do
      readSTRef conts.args >>= \case
        -- The continuation has already been followed at this position.
        HasBeenFollowed xsRef -> do
          modifySTRef xsRef (xs <>)
          parseCurrentStates env
        -- It hasn't.
        HasntBeenFollowed -> do
          xsRef <- newSTRef xs
          writeSTRef conts.args $ HasBeenFollowed xsRef
          ks <- simplifyCont conts
          res <- cacheResultsRef xsRef
          parseCurrentStates $
            env
              & addCurrentStates (map (contToState res) ks)
              & addReset (writeSTRef conts.args HasntBeenFollowed)

newtype Parser t a = Parser (forall s. [t] -> ST s (Result s t a))

-- | Create a parser from the given grammar.
parser :: (forall r. Grammar r (Prod r t a)) -> Parser t a
parser grammar =
  Parser \tokens -> do
    prod <- Grammar.runGrammar (fmap Prod.nonTerminal . mkRule) grammar
    state <- initialState prod
    parseCurrentState
      ParseEnv
        { tokens,
          offset = 0,
          names = [],
          states = [],
          nextStates = [],
          results = [],
          reset = pure ()
        }
      state
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
