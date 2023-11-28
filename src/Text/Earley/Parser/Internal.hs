-- | This module exposes the internals of the package: its API may change
-- independently of the PVP-compliant version number.
module Text.Earley.Parser.Internal where

import Control.Applicative
import Control.Monad
import Control.Monad.ST
import Data.Coerce (coerce)
import Data.STRef
import Data.Text (Text)
import Text.Earley.Grammar

-------------------------------------------------------------------------------
-- Concrete rules and productions
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
  computeNullsRef <- newSTRef do
    writeSTRef computeNullsRef $ pure []
    ns <- unResults $ prodNulls p
    writeSTRef computeNullsRef $ pure ns
    pure ns
  pure
    Rule
      { ruleProd = removeNulls p,
        ruleConts = c,
        ruleNulls = Results $ join $ readSTRef computeNullsRef
      }

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
-- Delayed results
-------------------------------------------------------------------------------

newtype Results s a = Results {unResults :: ST s [a]}
  deriving (Functor)

cacheResults :: forall s a. Results s a -> ST s (Results s a)
cacheResults =
  coerce @(ST s [a] -> ST s (ST s [a])) cached

-- Cache an action by returning an action that:
--
--   * when run for the first time, runs the given action and returns the result
--   * every time thereafter, returns the same result
cached :: ST s a -> ST s (ST s a)
cached action = mdo
  resultRef <-
    newSTRef do
      result <- action
      writeSTRef resultRef (pure result)
      pure result
  pure (join (readSTRef resultRef))

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
  | HasBeenFollowed (STRef s (Results s a))

data Conts s r t a b = Conts
  { conts :: !(STRef s [Cont s r t a b]),
    contsArgs :: !(STRef s (BeenFollowed s a))
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
    go !_ [Cont g (Pure f) args cont'] = do
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
  { -- | The final position in the input (0-based) that the
    -- parser reached.
    position :: Int,
    -- | The named productions processed at the final
    -- position.
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
  | -- | The parser parsed a number of @a@s.  These are given as a computation,
    -- @'ST' s [a]@ that constructs the 'a's when run.  We can thus save some
    -- work by ignoring this computation if we do not care about the results.
    -- The 'Int' is the position in the input where these results were
    -- obtained, the @i@ the rest of the input, and the last component is the
    -- continuation.
    Parsed [Results s a] Int [t] (ST s (Result s t a))
  deriving stock (Functor)

data ParseEnv s t a = ParseEnv
  { -- | Results ready to be reported (when this position has been processed)
    results :: ![Results s a],
    -- | States to process at the next position
    next :: ![State s a t a],
    -- | Computation that resets the continuation refs of productions
    reset :: !(ST s ()),
    -- | Named productions encountered at this position
    names :: ![Text],
    -- | The current position in the input string
    curPos :: !Int,
    -- | The input string
    input :: ![t]
  }

emptyParseEnv :: [t] -> ParseEnv s t a
emptyParseEnv input =
  ParseEnv
    { results = [],
      next = [],
      reset = pure (),
      names = [],
      curPos = 0,
      input
    }
{-# INLINE emptyParseEnv #-}

-- | The internal parsing routine
parse ::
  -- | States to process at this position
  [State s a t a] ->
  ParseEnv s t a ->
  ST s (Result s t a)
parse [] env@ParseEnv {results = [], next = []} = do
  reset env
  pure $
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
    (emptyParseEnv $ drop 1 $ input env) {curPos = curPos env + 1}
parse [] env = do
  reset env
  pure $
    Parsed (results env) (curPos env) (input env) $
      parse [] env {results = [], reset = return ()}
parse (st : ss) env = case st of
  Final res -> parse ss env {results = res : results env}
  State pr args pos scont -> case pr of
    Terminal f p ->
      case safeHead (input env) >>= f of
        Just a ->
          parse
            ss
            env {next = State p (args . ($ a)) Previous scont : next env}
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
    Pure a ->
      case pos of
        -- Skip following continuations that stem from the current position; such
        -- continuations are handled separately.
        Current -> parse ss env
        Previous -> do
          let argsRef = contsArgs scont
          masref <- readSTRef argsRef
          case masref of
            HasBeenFollowed asref -> do
              -- The continuation has already been followed at this position.
              modifySTRef asref $ mappend $ args a
              parse ss env
            HasntBeenFollowed -> do
              -- It hasn't.
              asref <- newSTRef $ args a
              writeSTRef argsRef $ HasBeenFollowed asref
              ks <- simplifyCont scont
              res <- cached $ join $ unResults <$> readSTRef asref
              let kstates = map (contToState (Results res)) ks
              parse
                (kstates ++ ss)
                env {reset = writeSTRef argsRef HasntBeenFollowed >> reset env}
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

safeHead :: [a] -> Maybe a
safeHead = \case
  [] -> Nothing
  x : _ -> Just x

newtype Parser t a = Parser (forall s. [t] -> ST s (Result s t a))

-- | Create a parser from the given grammar.
parser ::
  (forall r. Grammar r (Prod r t a)) ->
  Parser t a
parser g = Parser \i -> do
  s <- initialState =<< runGrammar (fmap nonTerminal . mkRule) g
  parse [s] (emptyParseEnv i)
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
        as <- runResults mas
        (bs, rep) <- go =<< k
        pure (map (,cpos) as ++ bs, rep)

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
            as <- runResults mas
            (bs, rep) <- go =<< k
            pure (as ++ bs, rep)
        | otherwise -> go =<< k
{-# INLINE fullParses #-}

runResults :: [Results s a] -> ST s [a]
runResults =
  fmap concat . unResults . sequence

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
