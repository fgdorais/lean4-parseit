# Lean 4 / ParseIt

A lean parser combinator library for [Lean 4](https://lean-lang.org/), built on iterators.

Parsers read tokens from any pure `Std.Iter`. The parser state is the iterator itself, so
backtracking is just reusing an earlier iterator. Every successful parse records whether it
consumed input, and this lets all repetition combinators be total: there is no `partial` in the
library, and repeating a parser that consumes nothing stops instead of looping forever.

Source documentation is available at
[www.dorais.org/lean4-parseit/doc/](https://www.dorais.org/lean4-parseit/doc/).

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

New to ParseIt? Start with the [tutorial](TUTORIAL.md). Coming from lean4-parser? See
[MIGRATION.md](MIGRATION.md).

## Overview

* `ParseIt.Basic`: the `ParserT` monad transformer, alternatives with `<|>` and `first`,
  `lookAhead`, `notFollowedBy`, the `option` family, and positions with `getPos` and `withSpan`.
* `ParseIt.Combinators`: token parsers and the `foldl`, `foldr`, `take`, `drop`, `count`, `sepBy`
  and `endBy` families.
* `ParseIt.Error`: the `Error` class with the `Trivial`, `Basic` and `Simple` error types.
* `ParseIt.Input`: inputs for `String.Slice`, `ByteArray`, `BitVec`, `Array`, `Vector` and `List`,
  with `parseString`, `parseSlice`, `parseByteArray`, `parseBitVec`, `parseArray`, `parseVector`
  and `parseList`.
* `ParseIt.ScalarArray`: inputs for the arrays of
  [lean4-scalar-arrays](https://github.com/fgdorais/lean4-scalar-arrays), with a runner for each
  array type, such as `parseUInt8Array` and `parseFloat64Array`, and `parseFloatArray` for core's
  `FloatArray`.
* `ParseIt.Char`: ASCII character and numeric parsers, and Unicode property parsers based on
  [UnicodeBasic](https://github.com/fgdorais/lean4-unicode-basic).
* `ParseIt.UTF` (experimental): parsers over UTF-8, UTF-16 and UTF-32 input, with `parseUTF8`,
  `parseUTF16` and `parseUTF32`, based on
  [UnicodeFormat](https://github.com/fgdorais/lean4-unicode-format). Errors are at positions in the
  encoded input, and ill-formed input is reported as an error, or consumed with `UTF.illFormed` by
  parsers that go on after it.

## Acknowledgements

ParseIt is inspired by [Lean 4 Parser](https://github.com/fgdorais/lean4-parser) by François G.
Dorais, Kyrill Serdyuk and Emma Shroyer.

-----

* ParseIt is copyright © 2026 François G. Dorais. The library is released under the
  [Apache 2.0 license](http://www.apache.org/licenses/LICENSE-2.0).
