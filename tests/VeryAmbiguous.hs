{-# LANGUAGE RecursiveDo, ScopedTypeVariables #-}
module VeryAmbiguous where
import Control.Applicative
import Debug.Trace
import Test.Tasty
import Test.Tasty.HUnit      as HU

import Text.Earley

tests :: TestTree
tests = testGroup "Very ambiguous"
  [ HU.testCase "Gives the right number of results" $
      length (fst $ fullParses (parser veryAmbiguous) $ replicate 8 'b') @?= 2871
  , HU.testCase "Gives the correct report" $
      report (parser veryAmbiguous) (replicate 3 'b') @?=
      Report {position = 3, expected = ["s"], unconsumed = ""}
  , HU.testCase "Parser agrees with generator" $ and (do
      n <- [3..3]
      let str = replicate n 'b'
          numParses = length (traceShowId $ fst $ fullParses (parser veryAmbiguous) str)
          numGens = length $ traceShowId $ exactly n $ generator veryAmbiguous "b"
      return $ trace ("numParses = " ++ show numParses) numParses == trace ("numGens = " ++ show numGens) numGens)
    @? "Parser agrees with generator"
  ]

veryAmbiguous :: Grammar r (Prod r Char ())
veryAmbiguous = mdo
  s <- rule $ () <$ token 'b'
           <|> () <$ s <* s
           <|> () <$ s <* s <* s
           <?> "s"
  return s
