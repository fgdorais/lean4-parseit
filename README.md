# ParseIt

A lean parser combinator library for [Lean 4](https://lean-lang.org/), built on iterators.

Parsers read tokens from any pure `Std.Iter`. The parser state is the iterator itself, so
backtracking is just reusing an earlier iterator. Every successful parse records whether it
consumed input, and this lets all repetition combinators be total: there is no `partial` in the
library, and repeating a parser that consumes nothing stops instead of looping forever.

## Usage

Add this dependency to your project's `lakefile.toml`:

```toml
[[require]]
name = "ParseIt"
git = "https://github.com/fgdorais/lean4-parseit"
rev = "main"
```

Then add `import ParseIt` at the top of any Lean file where you plan to use this library. For
example:

```lean
import ParseIt

open ParseIt ParseIt.Char

/-- Parses a list of sign-separated integers (no spaces) and returns their sum. -/
def parseSum : Parser (Error.Basic CharIterator) CharIterator Char Int :=
  foldl (· + ·) 0 ASCII.parseInt <* endOfInput

-- returns `some 42`
#eval parseSum.parseString "11-1+2-3+33" |>.toOption
```

The `ParseItExamples` directory contains more elaborate parsers: a BNF parser that parses its own syntax,
a JSON validator and a Roman numeral parser.

## Overview

* `ParseIt.Basic`: the `ParserT` monad transformer, alternatives with `<|>` and `first`,
  `lookAhead`, `notFollowedBy`, the `option` family, and positions with `getPos` and `withSpan`.
* `ParseIt.Combinators`: token parsers and the `foldl`, `foldr`, `take`, `drop`, `count`, `sepBy`
  and `endBy` families.
* `ParseIt.Error`: the `Error` class with the `Trivial`, `Basic` and `Simple` error types.
* `ParseIt.Input`: inputs for `String.Slice`, `ByteArray`, `BitVec`, `Array`, `Vector` and `List`,
  with `parseString`, `parseSlice`, `parseByteArray`, `parseBitVec`, `parseArray`, `parseVector`
  and `parseList`.
* `ParseIt.Char`: ASCII character and numeric parsers, and Unicode property parsers based on
  [UnicodeBasic](https://github.com/fgdorais/lean4-unicode-basic).

## Acknowledgements

ParseIt is inspired by [Lean 4 Parser](https://github.com/fgdorais/lean4-parser) by François G.
Dorais, Kyrill Serdyuk and Emma Shroyer.

-----

* ParseIt is copyright © 2026 François G. Dorais. The library is released under the
  [Apache 2.0 license](http://www.apache.org/licenses/LICENSE-2.0).
