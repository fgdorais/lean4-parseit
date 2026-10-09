# Migrating from lean4-parser

ParseIt keeps most of the combinator vocabulary of
[lean4-parser](https://github.com/fgdorais/lean4-parser), so most parsers port by changing imports,
types and the way they are run. This guide lists everything that differs.

## Imports and namespaces

| lean4-parser | ParseIt |
| --- | --- |
| `import Parser` | `import ParseIt` |
| `open Parser Char` | `open ParseIt ParseIt.Char` |
| `Parser.Char.ASCII.*`, `Parser.Char.Unicode.*` | `ParseIt.Char.ASCII.*`, `ParseIt.Char.Unicode.*` |

## Parser types

lean4-parser parses a `Parser.Stream σ τ`; ParseIt parses any pure iterator `Std.Iter (α := ι) τ`,
and the parser state is the iterator itself.

| lean4-parser | ParseIt |
| --- | --- |
| `ParserT ε σ τ m α` with `[Parser.Stream σ τ] [Parser.Error ε σ τ]` | `ParserT ε ι τ m α` with `[Std.Iterator ι Id τ]`, plus `[Error ε ι τ]` where errors are thrown |
| `Parser ε σ τ α` | `Parser ε ι τ α` |
| `SimpleParser String.Slice Char α` | `Parser (Error.Simple CharIterator) CharIterator Char α` |
| `BasicParser σ τ α` | `Parser (Error.Basic ι) ι τ α` |
| `TrivialParser σ τ α` | `Parser Error.Trivial ι τ α` |

There are no `SimpleParser`/`BasicParser`/`TrivialParser` abbreviations; define your own, for
example `abbrev P := Parser (Error.Simple CharIterator) CharIterator Char`.

Repetition combinators need `[Std.Iterators.Finite ι Id]`, and token parsers need
`[Std.Iterators.Productive ι Id]`. All iterators provided by ParseIt and core are finite.

## Inputs and running parsers

| lean4-parser input | ParseIt input |
| --- | --- |
| `String.Slice` | `CharIterator`, via `parseString`, `parseSlice` or `CharIterator.ofSlice` |
| `ByteSlice` | `ByteIterator` over a `ByteArray`, via `parseByteArray` |
| `Subarray τ` | `Array.iter`, via `parseArray`, or `parseVector` for `Vector` |
| `Parser.Stream.OfList` | `List.iter`, via `parseList` (no positions) |
| `Substring.Raw` | not supported |

`p.run s` returned `.ok stream value` or `.error stream err`. In ParseIt:

* `p.parseString s` (and the other `parse*` helpers) returns `Except ε α`.
* `p.run it` returns `Result ε it α`: `.ok rest progress value` or `.error err`. Errors carry no
  stream, since a failed parse never consumes input.
* To check that all input was consumed, end the parser with `<* endOfInput`.

## Errors

The `Error` class takes the iterator where the error happened instead of a stream position, and has
an extra `merge` method used by `<|>` and `first` to combine the errors of failed alternatives.

```lean
class Error (ε ι τ) [Iterator ι Id τ] where
  unexpected : Iter (α := ι) τ → Option τ → ε
  addMessage : ε → Iter (α := ι) τ → String → ε
  merge : ε → ε → ε := fun _ e => e
```

Positions come from the `HasPos ι τ` class, with `HasPos.pos it`. `CharIterator` positions are byte
offsets (`String.Pos.Raw`); byte, bit and array positions are indices (`Nat`).

* `Error.Basic` is a structure with fields `pos` and `token` instead of a pair, and keeps the error
  at the furthest position when merging.
* `Error.Simple` has a third constructor, `merge`, recording both failed alternatives.
* Errors are reported at the offending token, not after it.

## Combinators

Unchanged: `tokenMap`, `anyToken`, `tokenFilter`, `token`, `tokenArray`, `tokenList`, `lookAhead`,
`notFollowedBy`, `endOfInput`, `test`, `option!`, `option?`, `optional`, `first`, `foldl`,
`foldlM`, `foldlP`, `foldr`, the `take`, `drop` and `count` families, and the `sepBy` and `endBy`
families. `throwUnexpected`, `throwUnexpectedWithMessage` and `withErrorMessage` are also unchanged.

| lean4-parser | ParseIt |
| --- | --- |
| `withBacktracking p` | `p`: every parser backtracks on failure |
| `getPosition` | `getPos` (needs `HasPos`) |
| `withCapture p` | `withSpan p` for positions, or `captureSlice p` for the consumed `String.Slice` |
| `getStream`, `setStream`, `setPosition` | none; the input position can only move forward |
| `tokenCore next?` | `tokenMap` |
| `peek` | `lookAhead anyToken` |
| `optionM p d` | `optionD p d` |
| `optionD p x` | `optionD p (pure x)` |
| `eoption p` | `tryCatch (Sum.inl <$> p) (fun e => pure (.inr e))` |
| `efirst ps` | `first ps`, with `Error.Simple` to keep every error |
| `efoldlP`, `efoldlM`, `efoldl` | `foldlP`, `foldlM`, `foldl` |
| `throwErrorWithMessage e msg` | `throw e` inside `withErrorMessage msg` |

New in ParseIt: `foldlN`, `foldlUpTo` and `foldlUntil`, and the `parse*` helpers above.

### Results in any universe

ParseIt parsers live in one universe `u`, so results that lean4-parser returns as `Unit`, `Bool` or
`Nat` are `Unitᵤ`, `Boolᵤ` or `Natᵤ`: `notFollowedBy`, `optional`, `endOfInput` and the `drop`
family return `Unitᵤ`, `test` returns `Boolᵤ`, and the `count` family returns `Natᵤ`. These coerce
to `Bool` and `Nat` and print like them, so most code is unaffected. Comparisons such as
`(← count p) < 3` and dot notation need an ascription, `((← count p) : Nat) < 3`, or `.val`.

## Behavior changes

* **Repetition always terminates.** A repeated parser that succeeds without consuming input stops
  the repetition instead of looping forever. `takeUntil`, `dropUntil` and `countUntil` fail with
  the error from `stop` in that case.
* **Error merging.** `p <|> q` and `first` combine the errors of failed alternatives with
  `Error.merge`; lean4-parser kept only the last error.
* **`drop n p` and `dropUpTo n p`** consume no input on failure and stop early, as documented.
  Older lean4-parser versions got both wrong (fixed in fgdorais/lean4-parser#142).

## Character parsers

* `chars s` and the `String.Slice`-only `string s` are both `string s`, for any character iterator.
* `captureStr p` is `captureSlice p`.
* `RegEx` and `matchStr` have no equivalent.
* `Unicode.digit` accepts only decimal digits (general category Nd), not superscripts such as `²`.
* `Unicode.GeneralCategory.surrogate` is removed, since a Lean `Char` is never a surrogate.
* `Unicode.GeneralCategory.noncharacter` is `Unicode.GeneralCategory.unassigned`.
  `Unicode.noncharacter` is the `Noncharacter_Code_Point` property.
* New: `parseScript`, `parseScriptExt`, `defaultIgnorable`, `ascii`, `assigned`, `joinControl`,
  `charCaseInsensitive` and `stringCaseInsensitive`.

## Recursive grammars

Mutually recursive parsers are still `partial`, which needs an `Inhabited` instance for the parser
type:

```lean
instance {α} : Inhabited (P α) := ⟨throwUnexpected⟩
```

## Example

The README example of lean4-parser ports as follows.

```lean
import ParseIt

open ParseIt ParseIt.Char

abbrev SumParser := Parser (Error.Simple CharIterator) CharIterator Char

/-- Parses a list of sign-separated integers (no spaces) and returns their sum. -/
def parseSum : SumParser Int := do
  let mut sum : Int := 0
  -- parse until all input is consumed
  while ! (← test endOfInput) do
    -- parse an integer (decimal only) and add to sum
    sum := sum + (← ASCII.parseInt)
  return sum

-- returns `some 42`
#eval parseSum.parseString "11-1+2-3+33" |>.toOption
```

The `ParseItExamples` directory has ports of the BNF, JSON and Roman numeral examples.
