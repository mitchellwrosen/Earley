{-# LANGUAGE RecursiveDo, ScopedTypeVariables #-}
module InlineAlts where
import Control.Applicative
import Test.Tasty
import Test.Tasty.HUnit as HU

import Text.Earley

tests :: TestTree
tests = testGroup "Inline alternatives"
  [ HU.testCase "They work when parsed" $
      let input = "ababbbaaabaa" in
      allParses (parser inlineAlts) input @?= allParses (parser nonInlineAlts) input
  , HU.testCase "They work when generated" $
      take 1000 (language $ generator inlineAlts "ab") @?=
      take 1000 (language $ generator nonInlineAlts "ab")
  ]

inlineAlts :: Grammar r (Prod r Char String)
inlineAlts = mdo
  p <- rule $ pure []
           <|> (:) <$> ((token 'a' <?> "a") <|> (token 'b' <?> "b")) <*> p
  return p

nonInlineAlts :: Grammar r (Prod r Char String)
nonInlineAlts = mdo
  ab <- rule $ (token 'a' <?> "a") <|> (token 'b' <?> "b")
  p  <- rule $ pure [] <|> (:) <$> ab <*> p
  return p
