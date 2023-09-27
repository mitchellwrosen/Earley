{-# LANGUAGE RecursiveDo, ScopedTypeVariables #-}
module Optional where
import Control.Applicative
import Test.Tasty
import Test.Tasty.HUnit as HU

import Text.Earley

tests :: TestTree
tests = testGroup "Optional"
  [ HU.testCase "Nothing" $
      fullParses (parser $ return optional_) "b"
      @?= (,) [(Nothing, 'b')] Report {position = 1, expected = [], unconsumed = ""}
  , HU.testCase "Just" $
      fullParses (parser $ return optional_) "ab"
      @?= (,) [(Just 'a', 'b')] Report {position = 2, expected = [], unconsumed = ""}
  , HU.testCase "Using rules Nothing" $
      fullParses (parser optionalRule) "b"
      @?= (,) [(Nothing, 'b')] Report {position = 1, expected = [], unconsumed = ""}
  , HU.testCase "Using rules Just" $
      fullParses (parser optionalRule) "ab"
      @?= (,) [(Just 'a', 'b')] Report {position = 2, expected = [], unconsumed = ""}
  , HU.testCase "Without continuation Nothing" $
      fullParses (parser $ return $ optional $ token 'a' <?> "a") ""
      @?= (,) [Nothing] Report {position = 0, expected = ["a"], unconsumed = ""}
  , HU.testCase "Without continuation Just" $
      fullParses (parser $ return $ optional $ token 'a' <?> "a") "a"
      @?= (,) [Just 'a'] Report {position = 1, expected = [], unconsumed = ""}
  , HU.testCase "Using rules without continuation Nothing" $
      fullParses (parser $ rule $ optional $ token 'a' <?> "a") ""
      @?= (,) [Nothing] Report {position = 0, expected = ["a"], unconsumed = ""}
  , HU.testCase "Using rules without continuation Just" $
      fullParses (parser $ rule $ optional $ token 'a' <?> "a") "a"
      @?= (,) [Just 'a'] Report {position = 1, expected = [], unconsumed = ""}
  , HU.testCase "Generate optional" $
      language (generator (return optional_) "ab")
      @?= [((Nothing, 'b'), "b"), ((Just 'a', 'b'), "ab")]
  , HU.testCase "Generate optional using rules" $
      language (generator optionalRule "ab")
      @?= [((Nothing, 'b'), "b"), ((Just 'a', 'b'), "ab")]
  , HU.testCase "Generate optional without continuation" $
      language (generator (return $ optional $ token 'a' <?> "a") "ab")
      @?= [(Nothing, ""), (Just 'a', "a")]
  , HU.testCase "Generate optional using rules without continuation" $
      language (generator (rule $ optional $ token 'a' <?> "a") "ab")
      @?= [(Nothing, ""), (Just 'a', "a")]
  ]

optional_ :: Prod r Char (Maybe Char, Char)
optional_ = (,) <$> optional (token 'a' <?> "a") <*> (token 'b' <?> "b")

optionalRule :: Grammar r (Prod r Char (Maybe Char, Char))
optionalRule = mdo
  test <- rule $ (,) <$> optional (token 'a' <?> "a") <*> (token 'b' <?> "b")
  return test
