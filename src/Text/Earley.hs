-- | Parsing all context-free grammars using Earley's algorithm.
module Text.Earley
  ( -- * Context-free grammars
    Prod,
    terminal,
    (<?>),
    Grammar,
    rule,

    -- * Derived operators
    satisfy,
    token,
    anyToken,
    list,
    matches,

    -- * Parsing
    Report (..),
    Parser.Result (..),
    Parser,
    parser,
    allParses,
    fullParses,

    -- * Recognition
    report,

    -- * Language generation
    Generator,
    generator,
    language,
    upTo,
    exactly,
  )
where

import Text.Earley.Derived
import Text.Earley.Generator
import Text.Earley.Grammar
import Text.Earley.Parser as Parser
import Text.Earley.Prod (Prod, terminal, (<?>))
