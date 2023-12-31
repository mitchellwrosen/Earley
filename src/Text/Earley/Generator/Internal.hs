-- | This module exposes the internals of the package: its API may change
-- independently of the PVP-compliant version number.
module Text.Earley.Generator.Internal where

import Control.Applicative
import Control.Monad
import Control.Monad.ST.Lazy
import Data.Maybe (mapMaybe)
import Data.STRef.Lazy
import Text.Earley.Grammar
import Text.Earley.Prod (Prod)
import Text.Earley.Prod qualified as Prod

-------------------------------------------------------------------------------
-- Concrete rules and productions
-------------------------------------------------------------------------------

-- | The concrete rule type that the generator uses
data Rule s r t a = Rule
  { ruleProd :: ProdR s r t a,
    ruleConts :: !(STRef s (STRef s [Cont s r t a r])),
    ruleNulls :: !(Results s t a)
  }

mkRule :: ProdR s r t a -> ST s (Rule s r t a)
mkRule p = mdo
  c <- newSTRef =<< newSTRef mempty
  computeNullsRef <- newSTRef do
    writeSTRef computeNullsRef $ return []
    ns <- unResults $ prodNulls p
    writeSTRef computeNullsRef $ return ns
    return ns
  return $ Rule (removeNulls p) c (Results $ join $ readSTRef computeNullsRef)

prodNulls :: ProdR s r t a -> Results s t a
prodNulls prod = case prod of
  Prod.Terminal {} -> empty
  Prod.NonTerminal r p -> ruleNulls r <**> prodNulls p
  Prod.Pure a -> pure a
  Prod.Alts as p -> mconcat (map prodNulls as) <**> prodNulls p
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

resetConts :: Rule s r t a -> ST s ()
resetConts r = writeSTRef (ruleConts r) =<< newSTRef mempty

-------------------------------------------------------------------------------
-- Delayed results
-------------------------------------------------------------------------------

newtype Results s t a = Results {unResults :: ST s [(a, [t])]}
  deriving (Functor)

lazyResults :: ST s [(a, [t])] -> ST s (Results s t a)
lazyResults stas = mdo
  resultsRef <- newSTRef do
    as <- stas
    writeSTRef resultsRef $ pure as
    pure as
  pure $ Results $ join $ readSTRef resultsRef

instance Applicative (Results s t) where
  pure x = Results $ pure [(x, mempty)]
  (<*>) = ap

instance Alternative (Results t s) where
  empty = Results $ pure []
  Results sxs <|> Results sys = Results $ (<|>) <$> sxs <*> sys

instance Monad (Results t s) where
  return = pure
  Results stxs >>= f = Results $ do
    xs <- stxs
    concat <$> mapM (\(x, ts) -> fmap (\(y, ts') -> (y, ts' ++ ts)) <$> unResults (f x)) xs

instance Semigroup (Results s t a) where
  (<>) = (<|>)

instance Monoid (Results s t a) where
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
    !(a -> Results s t b) ->
    !BirthPos ->
    !(Conts s r t b c) ->
    State s r t c
  Final :: !(Results s t a) -> State s r t a

-- | A continuation accepting an @a@ and producing a @b@.
data Cont s r t a b where
  Cont ::
    !(a -> Results s t b) ->
    !(ProdR s r t (b -> c)) ->
    !(c -> Results s t d) ->
    !(Conts s r t d e') ->
    Cont s r t a e'
  FinalCont :: (a -> Results s t c) -> Cont s r t a c

data Conts s r t a c = Conts
  { conts :: !(STRef s [Cont s r t a c]),
    contsArgs :: !(STRef s (Maybe (STRef s (Results s t a))))
  }

newConts :: STRef s [Cont s r t a c] -> ST s (Conts s r t a c)
newConts r = Conts r <$> newSTRef Nothing

contraMapCont :: (b -> Results s t a) -> Cont s r t a c -> Cont s r t b c
contraMapCont f (Cont g p args cs) = Cont (f >=> g) p args cs
contraMapCont f (FinalCont args) = FinalCont (f >=> args)

contToState :: BirthPos -> Results s t a -> Cont s r t a c -> State s r t c
contToState pos r (Cont g p args cs) = State p (\f -> r >>= g >>= args . f) pos cs
contToState _ r (FinalCont args) = Final $ r >>= args

-- | Strings of non-ambiguous continuations can be optimised by removing indirections.
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
-- Generation
-------------------------------------------------------------------------------

-- | The result of a generator.
data Result s t a
  = -- | The generator ended.
    Ended (ST s [(a, [t])])
  | -- | The generator produced a number of @a@s.  These are given as a
    -- computation, @'ST' s [a]@ that constructs the 'a's when run.  The 'Int' is
    -- the position in the input where these results were obtained, and the last
    -- component is the continuation.
    Generated (ST s [(a, [t])]) (ST s (Result s t a))
  deriving (Functor)

data GenerationEnv s t a = GenerationEnv
  { -- | Results ready to be reported (when this position has been processed)
    results :: ![ST s [(a, [t])]],
    -- | States to process at the next position
    next :: ![State s a t a],
    -- | Computation that resets the continuation refs of productions
    reset :: !(ST s ()),
    -- | The possible tokens
    tokens :: ![t]
  }

{-# INLINE emptyGenerationEnv #-}
emptyGenerationEnv :: [t] -> GenerationEnv s t a
emptyGenerationEnv ts =
  GenerationEnv
    { results = mempty,
      next = mempty,
      reset = return (),
      tokens = ts
    }

-- | The internal generation routine
generate ::
  -- | States to process at this position
  [State s a t a] ->
  GenerationEnv s t a ->
  ST s (Result s t a)
generate [] env@GenerationEnv {next = []} = do
  reset env
  return $ Ended $ concat <$> sequence (results env)
generate [] env = do
  reset env
  return $
    Generated (concat <$> sequence (results env)) $
      generate (next env) $
        emptyGenerationEnv $
          tokens env
generate (st : ss) env = case st of
  Final res -> generate ss env {results = unResults res : results env}
  State pr args pos scont -> case pr of
    Prod.Terminal f p ->
      generate
        ss
        env
          { next =
              [State p (\g -> Results (pure $ map (\(t, a) -> (g a, [t])) xs) >>= args) Previous scont | xs <- [mapMaybe (\t -> (,) t <$> f t) $ tokens env], not $ null xs]
                ++ next env
          }
    Prod.NonTerminal r p -> do
      rkref <- readSTRef $ ruleConts r
      ks <- readSTRef rkref
      writeSTRef rkref (Cont pure p args scont : ks)
      ns <- unResults $ ruleNulls r
      let addNullState
            | null ns = id
            | otherwise =
                (:) $
                  State p (\f -> Results (pure ns) >>= args . f) pos scont
      if null ks
        then do
          -- The rule has not been expanded at this position.
          st' <- State (ruleProd r) pure Current <$> newConts rkref
          generate
            (addNullState $ st' : ss)
            env {reset = resetConts r >> reset env}
        else -- The rule has already been expanded at this position.
          generate (addNullState ss) env
    Prod.Pure a
      -- Skip following continuations that stem from the current position; such
      -- continuations are handled separately.
      | pos == Current -> generate ss env
      | otherwise -> do
          let argsRef = contsArgs scont
          masref <- readSTRef argsRef
          case masref of
            Just asref -> do
              -- The continuation has already been followed at this position.
              modifySTRef asref $ mappend $ args a
              generate ss env
            Nothing -> do
              -- It hasn't.
              asref <- newSTRef $ args a
              writeSTRef argsRef $ Just asref
              ks <- simplifyCont scont
              res <- lazyResults $ unResults =<< readSTRef asref
              let kstates = map (contToState pos res) ks
              generate
                (kstates ++ ss)
                env {reset = writeSTRef argsRef Nothing >> reset env}
    Prod.Alts as (Prod.Pure f) -> do
      let args' = args . f
          sts = [State a args' pos scont | a <- as]
      generate (sts ++ ss) env
    Prod.Alts as p -> do
      scont' <- newConts =<< newSTRef [Cont pure p args scont]
      let sts = [State a pure Previous scont' | a <- as]
      generate (sts ++ ss) env
    Prod.Many p q -> mdo
      r <- mkRule $ pure [] <|> (:) <$> p <*> Prod.NonTerminal r (Prod.Pure id)
      generate (State (Prod.NonTerminal r q) args pos scont : ss) env
    Prod.Named pr' _ -> generate (State pr' args pos scont : ss) env

type Generator t a = forall s. ST s (Result s t a)

-- | Create a language generator for given grammar and list of allowed tokens.
generator ::
  (forall r. Grammar r (Prod r t a)) ->
  [t] ->
  Generator t a
generator g ts = do
  let nt x = Prod.NonTerminal x $ pure id
  s <- initialState =<< runGrammar (fmap nt . mkRule) g
  generate [s] $ emptyGenerationEnv ts

-- | Run a generator, returning all members of the language.
--
-- The members are returned as parse results paired with the list of tokens
-- used to produce the result.
-- The elements of the returned list of results are sorted by their length in
-- ascending order.  If there are multiple results of the same length they are
-- returned in an unspecified order.
language ::
  Generator t a ->
  [(a, [t])]
language gen = runST $ gen >>= go
  where
    go :: Result s t a -> ST s [(a, [t])]
    go r = case r of
      Ended mas -> mas
      Generated mas k -> do
        as <- mas
        (as ++) <$> (go =<< k)

-- | @upTo n gen@ runs the generator @gen@, returning all members of the
-- language that are of length less than or equal to @n@.
--
-- The members are returned as parse results paired with the list of tokens
-- used to produce the result.
-- The elements of the returned list of results are sorted by their length in
-- ascending order.  If there are multiple results of the same length they are
-- returned in an unspecified order.
upTo ::
  Int ->
  Generator t a ->
  [(a, [t])]
upTo len gen = runST $ gen >>= go 0
  where
    go :: Int -> Result s t a -> ST s [(a, [t])]
    go curLen r | curLen <= len = case r of
      Ended mas -> mas
      Generated mas k -> do
        as <- mas
        (as ++) <$> (go (curLen + 1) =<< k)
    go _ _ = return []

-- | @exactly n gen@ runs the generator @gen@, returning all members of the
-- language that are of length equal to @n@.
--
-- The members are returned as parse results paired with the list of tokens
-- used to produce the result.
-- If there are multiple results they are returned in an unspecified order.
exactly ::
  Int ->
  Generator t a ->
  [(a, [t])]
exactly len _ | len < 0 = []
exactly len gen = runST $ gen >>= go 0
  where
    go :: Int -> Result s t a -> ST s [(a, [t])]
    go !curLen r = case r of
      Ended mas
        | curLen == len -> mas
        | otherwise -> return []
      Generated mas k
        | curLen == len -> mas
        | otherwise -> go (curLen + 1) =<< k
