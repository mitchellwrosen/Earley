{-# LANGUAGE FlexibleContexts, RankNTypes, RecursiveDo, ScopedTypeVariables #-}
module UnbalancedPars where

import Data.Char (isAlpha)

import Control.Applicative
import Test.Tasty
import Test.Tasty.HUnit      as HU

import Text.Earley

tests :: TestTree
tests = testGroup "Unbalanced parentheses"
  [ HU.testCase "Parses balanced" $
      fst (fullParses' unbalancedPars
        "((x))") @?= [(b . b) x]
  , HU.testCase "Parses one unbalanced" $
      fst (fullParses' unbalancedPars
        "((x)") @?= [(u . b) x]
  , HU.testCase "Parses two unbalanced" $
      fst (fullParses' unbalancedPars
        "((x") @?= [(u . u) x]
  ]
  where
    -- [b]alanced
    b :: Expr -> Expr
    b e = ExprInBrackets "(" e ")"

    -- [u]nbalanced
    u :: Expr -> Expr
    u e = ExprInBrackets "(" e ""

    -- [x] variable
    x :: Expr
    x = Var 'x'

data Token = EOF | Char !Char
  deriving (Eq, Ord, Show)

fullParses'
  :: (forall r. Grammar r (Prod r Token a))
  -> String
  -> ([a], Report Char)
fullParses' g s =
  let (res, rep) = allParses (parser $ (<* eof) <$> g) $ fmap Char s ++ repeat EOF
  in
    ( fst <$> res
    , rep { unconsumed = go $ unconsumed rep }
    )
  where
    go (Char c:xs) = c : go xs
    go _ = []

data Expr =
  Var Char | ExprInBrackets String Expr String
  deriving (Eq, Ord, Show)

eof :: Prod r Token Token
eof = token EOF

leftPar :: Prod r Token String
leftPar = "(" <$ token (Char '(')

rightPar :: Prod r Token String
rightPar = ")" <$ token (Char ')')

var :: Prod r Token Expr
var = terminal $ \t -> case t of
  Char c | isAlpha c -> Just $ Var c
  _ -> Nothing

unbalancedPars :: Grammar r (Prod r Token Expr)
unbalancedPars = mdo
  expr <- rule $ var <|> exprInBrackets
  exprInBrackets <- rule $
    ExprInBrackets
      <$> leftPar
      <*> expr
      <*> (rightPar <|> ("" <$ eof))
      <?> "parenthesized expression"
  return expr
