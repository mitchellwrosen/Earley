-- | This module exposes the internals of the package: its API may change
-- independently of the PVP-compliant version number.
module Text.Earley.Generator.Internal where

import Control.Applicative
import Control.Monad
import Control.Monad.ST.Lazy
import Data.Maybe (mapMaybe)
import Data.STRef.Lazy
import Text.Earley.Grammar
import Text.Earley.Results

-------------------------------------------------------------------------------

-- * Concrete rules and productions

-------------------------------------------------------------------------------

-- | The concrete rule type that the generator uses
data Rule s r t a = Rule
  { ruleProd :: ProdR s r t a,
    ruleConts :: !(STRef s (STRef s [Cont s r t a r])),
    ruleNulls :: !(Results s (F t) a)
  }

mkRule :: ProdR s r t a -> ST s (Rule s r t a)
mkRule p = mdo
  c <- newSTRef =<< newSTRef mempty
  computeNullsRef <- newSTRef do
    writeSTRef computeNullsRef (pure [])
    ns <- unResults (prodNulls p)
    writeSTRef computeNullsRef (pure ns)
    pure ns
  pure
    Rule
      { ruleProd = removeNulls p,
        ruleConts = c,
        ruleNulls = Results (join (readSTRef computeNullsRef))
      }

prodNulls :: ProdR s r t a -> Results s (F t) a
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
  Alts as (Pure f) -> alts (map removeNulls as) (Pure f)
  Alts {} -> prod
  Many {} -> prod
  Named p n -> Named (removeNulls p) n

type ProdR s r t a = Prod (Rule s r) t a

resetConts :: Rule s r t a -> ST s ()
resetConts r = writeSTRef (ruleConts r) =<< newSTRef mempty

-------------------------------------------------------------------------------

-- * Delayed results

-------------------------------------------------------------------------------

data T a
  = T0
  | T1 a
  | T2 !(T a) !(T a)

newtype F t a
  = F (a, T t)
  deriving stock (Functor)

instance Applicative (F t) where
  pure x = F (x, T0)
  (<*>) = ap

instance Monad (F t) where
  return = pure
  F (x, ts0) >>= f =
    let F (y, ts1) = f x
        !ts2 = combine ts0 ts1
     in F (y, ts2)
    where
      combine tx ty =
        case (tx, ty) of
          (T0, _) -> ty
          (_, T0) -> tx
          _ -> T2 ty tx -- yes swapped, so tokens come out in the right order

instance Foldable (F t) where
  foldr f z (F (x, _)) =
    f x z

instance Traversable (F t) where
  traverse f (F (x, ys)) =
    (\y -> F (y, ys)) <$> f x

streamF :: F t a -> (a, [t])
streamF (F (x, ts)) =
  (x, streamTs [ts])

streamTs :: [T a] -> [a]
streamTs = \case
  [] -> []
  T0 : xs -> streamTs xs
  T1 x : xs -> x : streamTs xs
  T2 xs ys : zs -> streamTs (xs : ys : zs)

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
    !(a -> Results s (F t) b) ->
    !BirthPos ->
    !(Conts s r t b c) ->
    State s r t c
  Final :: !(Results s (F t) a) -> State s r t a

-- | A continuation accepting an @a@ and producing a @b@.
data Cont s r t a b where
  Cont ::
    !(a -> Results s (F t) b) ->
    !(ProdR s r t (b -> c)) ->
    !(c -> Results s (F t) d) ->
    !(Conts s r t d e') ->
    Cont s r t a e'
  FinalCont :: (a -> Results s (F t) c) -> Cont s r t a c

data Conts s r t a c = Conts
  { conts :: !(STRef s [Cont s r t a c]),
    contsArgs :: !(STRef s (Maybe (STRef s (Results s (F t) a))))
  }

newConts :: STRef s [Cont s r t a c] -> ST s (Conts s r t a c)
newConts r = Conts r <$> newSTRef Nothing

contraMapCont :: (b -> Results s (F t) a) -> Cont s r t a c -> Cont s r t b c
contraMapCont f (Cont g p args cs) = Cont (f >=> g) p args cs
contraMapCont f (FinalCont args) = FinalCont (f >=> args)

contToState :: BirthPos -> Results s (F t) a -> Cont s r t a c -> State s r t c
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

-- * Generation

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
  deriving stock (Functor)

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

emptyGenerationEnv :: [t] -> GenerationEnv s t a
emptyGenerationEnv tokens =
  GenerationEnv
    { results = [],
      next = [],
      reset = pure (),
      tokens
    }
{-# INLINE emptyGenerationEnv #-}

-- | The internal generation routine
generate ::
  -- | States to process at this position
  [State s a t a] ->
  GenerationEnv s t a ->
  ST s (Result s t a)
generate [] env@GenerationEnv {next = []} = do
  reset env
  pure $ Ended $ concat <$> sequence (results env)
generate [] env = do
  reset env
  pure $
    Generated (concat <$> sequence (results env)) $
      generate (next env) $
        emptyGenerationEnv $
          tokens env
generate (st : ss) env = case st of
  Final res -> generate ss env {results = (map streamF <$> unResults res) : results env}
  State pr args pos scont -> case pr of
    Terminal f p ->
      generate
        ss
        env
          { next =
              [ State
                  p
                  (\g -> Results (pure $ map (\(t, a) -> F (g a, T1 t)) xs) >>= args)
                  Previous
                  scont
                | xs <- [mapMaybe (\t -> (,) t <$> f t) $ tokens env],
                  not $ null xs
              ]
                ++ next env
          }
    NonTerminal r p -> do
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
    Pure a
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
    Alts as (Pure f) -> do
      let args' = args . f
          sts = [State a args' pos scont | a <- as]
      generate (sts ++ ss) env
    Alts as p -> do
      scont' <- newConts =<< newSTRef [Cont pure p args scont]
      let sts = [State a pure Previous scont' | a <- as]
      generate (sts ++ ss) env
    Many p q -> mdo
      r <- mkRule $ pure [] <|> (:) <$> p <*> nonTerminal r
      generate (State (NonTerminal r q) args pos scont : ss) env
    Named pr' _ -> generate (State pr' args pos scont : ss) env

type Generator t a = forall s. ST s (Result s t a)

-- | Create a language generator for given grammar and list of allowed tokens.
generator ::
  (forall r. Grammar r (Prod r t a)) ->
  [t] ->
  Generator t a
generator g ts = do
  s <- initialState =<< runGrammar (fmap nonTerminal . mkRule) g
  generate [s] $ emptyGenerationEnv ts

nonTerminal :: r t a -> Prod r t a
nonTerminal x =
  NonTerminal x (Pure id)

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
language gen = runST (gen >>= go)
  where
    go :: Result s t a -> ST s [(a, [t])]
    go = \case
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
upTo len gen = runST (gen >>= go 0)
  where
    go :: Int -> Result s t a -> ST s [(a, [t])]
    go curLen
      | curLen <= len = \case
          Ended mas -> mas
          Generated mas k -> do
            as <- mas
            (as ++) <$> (go (curLen + 1) =<< k)
      | otherwise = const (pure [])

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
exactly len gen = runST (gen >>= go 0)
  where
    go :: Int -> Result s t a -> ST s [(a, [t])]
    go !curLen
      | curLen == len = \case
          Ended mas -> mas
          Generated mas _ -> mas
      | otherwise = \case
          Ended _ -> pure []
          Generated _ k -> go (curLen + 1) =<< k
