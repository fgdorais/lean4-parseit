# ParseIt tutorial

This tutorial builds up the main ideas of ParseIt step by step, ending with a small calculator. It
assumes you know some Lean 4, including `do` notation, but no prior experience with parser
combinators. Every example below is checked by the test file
[`ParseItTest/Tutorial.lean`](ParseItTest/Tutorial.lean).

To follow along, add ParseIt to your project as described in the [README](README.md), and start a
file with:

```lean
import ParseIt

open ParseIt ParseIt.Char
```

## Your first parser

A parser has type `Parser ε ι τ α`, where:

* `τ` is the type of tokens, here `Char`;
* `ι` is the iterator that produces the tokens, here `CharIterator`, which reads a string;
* `ε` is the type of errors, here `Error.Basic CharIterator`, which records where parsing failed;
* `α` is the type of the value returned by a successful parse.

The first three parameters rarely change within a project, so it is convenient to fix them once:

```lean
abbrev P := Parser (Error.Basic CharIterator) CharIterator Char
```

The parser `string s` accepts exactly the characters of `s`. Run a parser on a string with
`parseString`, which returns an `Except ε α`:

```lean
def hello : P String := string "hello"

#eval hello.parseString "hello world" |>.toOption -- some "hello"
#eval hello.parseString "help" |>.toOption        -- none
```

The first parse succeeds even though `" world"` is left over: a parser reads only as much input as
it needs. To require that the whole input is consumed, end the parser with `<* endOfInput`.

Other basic parsers include `char c` for a single character, `anyToken` for any one token,
`tokenFilter test` for a token that satisfies `test`, and the ASCII character classes such as
`ASCII.alpha`, `ASCII.digit` and `ASCII.whitespace`.

## Sequencing

Parsers form a monad, so `do` notation runs parsers one after the other, each starting where the
previous one stopped:

```lean
def pair : P (Nat × Nat) := do
  let x ← ASCII.parseNat
  discard <| char ','
  let y ← ASCII.parseNat
  return (x, y)

#eval pair.parseString "12,34" |>.toOption -- some (12, 34)
```

The usual applicative operators work too. `p <* q` runs both and keeps the result of `p`, `p *> q`
keeps the result of `q`, and `f <$> p` applies `f` to the result of `p`. This definition is
equivalent to the one above:

```lean
def pair' : P (Nat × Nat) :=
  Prod.mk <$> ASCII.parseNat <* char ',' <*> ASCII.parseNat
```

## Alternatives and backtracking

`p <|> q` tries `p`, and if `p` fails, tries `q` from the same starting point:

```lean
def keyword : P String := string "let" <|> string "lex"

#eval keyword.parseString "lex" |>.toOption -- some "lex"
```

Here `string "let"` reads `le` before failing on `x`, and `string "lex"` still starts from the
beginning. In ParseIt every parser backtracks on failure: a parser that fails consumes no input, so
there is no need for a `try` combinator as in Parsec. This is cheap because the parser state is just
an iterator, and backtracking reuses an earlier iterator value.

`first ps` tries each parser in the list `ps` in order. Since `pure x` always succeeds, it makes a
good default at the end of the list:

```lean
def sign : P Int := first [char '+' *> pure 1, char '-' *> pure (-1), pure 1]

#eval sign.parseString "-" |>.toOption -- some (-1)
#eval sign.parseString "7" |>.toOption -- some 1
```

The `option` family handles optional input: `option? p` returns `some x` or `none`, `optional p`
ignores the result, and `test p` returns whether `p` succeeded. None of these ever fail.

## Repetition

`takeMany p` parses `p` as many times as possible and returns an array of the results;
`takeMany1 p` requires at least one occurrence. `sepBy sep p` parses occurrences of `p` separated by
`sep`. The `take`, `drop`, `count`, `sepBy` and `endBy` families offer variants that collect,
ignore or count results.

Often it is better to combine results as they are parsed instead of collecting them in an array.
`foldl f init p` does this, starting from `init` and combining with `f`:

```lean
def word : P String := do
  let c ← ASCII.alpha
  foldl String.push c.toString ASCII.alpha

def words : P (Array String) := sepBy (char ' ') word

#eval words.parseString "parse it now" |>.toOption -- some #["parse", "it", "now"]

def digitSum : P Nat := foldl (fun n (d : Fin 10) => n + d) 0 ASCII.digit

#eval digitSum.parseString "1234" |>.toOption -- some 10
```

Repetition in ParseIt always terminates. Every successful parse records whether it consumed input,
and a repetition stops right after an occurrence that consumed nothing. In many parser libraries,
repeating a parser that can succeed without consuming input either loops forever or is a runtime
error. In ParseIt it simply stops:

```lean
def maybeAs : P (Array (Option Char)) := takeMany (option? (char 'a'))

#eval maybeAs.parseString "aab" |>.toOption -- some #[some 'a', some 'a', none]
```

## A calculator

Let's put these pieces together to evaluate arithmetic expressions such as `2 * (3 + 4)`, with the
usual precedence rules and with spaces allowed between tokens.

A common way to deal with spaces is to skip them after each token. The helper `lexeme p` parses `p`
followed by any amount of whitespace:

```lean
def ws : P Unit := dropMany ASCII.whitespace

def lexeme {α} (p : P α) : P α := p <* ws

def symbol (c : Char) : P Char := lexeme (char c)

def number : P Int := lexeme (Int.ofNat <$> ASCII.parseNat)
```

Operators are parsers that return the function they stand for:

```lean
def addOp : P (Int → Int → Int) :=
  first [symbol '+' *> pure (· + ·), symbol '-' *> pure (· - ·)]

def mulOp : P (Int → Int → Int) :=
  symbol '*' *> pure (· * ·)
```

The grammar has three levels: an expression is a sum of terms, a term is a product of factors, and a
factor is a number, a parenthesized expression or a negated factor. Sums and products are left folds
over the operators: `foldlP f init p` is like `foldl`, except that `f` is itself a parser, which
here parses the right operand and applies the operator:

```lean
instance {α} : Inhabited (P α) := ⟨throwUnexpected⟩

mutual

partial def expr : P Int := do
  foldlP (fun x op => op x <$> term) (← term) addOp

partial def term : P Int := do
  foldlP (fun x op => op x <$> factor) (← factor) mulOp

partial def factor : P Int :=
  first [
    number,
    symbol '(' *> expr <* symbol ')',
    symbol '-' *> Int.neg <$> factor]

end
```

The three parsers refer to each other, so they are `partial`, and Lean needs an `Inhabited`
instance for the parser type to accept them. Any parser will do; `throwUnexpected` is a parser that
always fails. Note that the repetitions inside these parsers are still total; only the recursion
through `factor` is `partial`.

Finally, skip leading whitespace, require that all input is consumed, and turn errors into
messages:

```lean
def calculate (s : String) : Except String Int :=
  match (ws *> expr <* endOfInput).parseString s with
  | .ok n => .ok n
  | .error e => .error s!"unexpected input at byte {e.pos.byteIdx}"

#eval calculate "1 + 2 * 3"     -- .ok 7
#eval calculate " (1 + 2) * 3 " -- .ok 9
#eval calculate "2 * -(3 - 10)" -- .ok 14
#eval calculate "10 - 4 - 3"    -- .ok 3
```

## Errors

The error type is a parameter of the parser, and ParseIt provides three:

* `Error.Trivial` records nothing. Use it when you only need to know whether parsing succeeded.
* `Error.Basic` records the position and the offending token. When alternatives fail, it keeps the
  error that got furthest into the input.
* `Error.Simple` records everything: the errors of all failed alternatives, and the messages added
  with `withErrorMessage msg p`.

You can also write your own instance of the `Error` class.

The calculator reports byte positions:

```lean
#eval calculate "1 + 2 x" -- .error "unexpected input at byte 6"
#eval calculate "1 + )"   -- .error "unexpected input at byte 2"
```

The second error may be surprising: the problem is the `)` at byte 4, yet the error is reported at
the `+`. This is how repetition interacts with backtracking. In `expr`, the round that parses `+ )`
fails, so `foldlP` backtracks to just before the `+` and returns the sum so far, `1`. Then
`endOfInput` fails at the `+`. The same happens with `takeMany`, `sepBy` and the other repetition
combinators: an occurrence that fails partway is not consumed. Some combinators, such as `sepBy`
and `endBy`, have a `strict` option that reports the error of such an occurrence instead.

## Positions and captured text

`getPos` returns the current position, and `withSpan p` returns the result of `p` together with the
positions where `p` started and stopped. For a `CharIterator` positions are byte offsets
(`String.Pos.Raw`); for byte, bit and array inputs they are indices.

```lean
def numberSpan : P (Nat × Nat) := do
  let (_, start, stop) ← withSpan number
  return (start.byteIdx, stop.byteIdx)

#eval numberSpan.parseString "42  + 1" |>.toOption -- some (0, 4)
```

The span of `number` includes the whitespace skipped by `lexeme`.

When parsing strings, `captureSlice p` returns the text that `p` consumed as a `String.Slice`, a
view into the input that copies nothing. This is a convenient way to read identifiers:

```lean
def ident : P String := lexeme do
  let (_, s) ← captureSlice (ASCII.alpha *> dropMany ASCII.alphanum)
  return s.copy

#eval ident.parseString "x1 = 2" |>.toOption -- some "x1"
```

## Other inputs

Parsers work with any pure `Std.Iter`, not just strings. ParseIt provides `parseByteArray`,
`parseBitVec`, `parseArray`, `parseVector` and `parseList`, and token parsers such as `token`,
`tokenFilter` and `tokenMap` work with any token type.

For example, a parser can read the output of a separate lexer. Here the tokens form an inductive
type and are read from an array:

```lean
inductive Tok where
  | num (n : Nat)
  | plus
deriving BEq

abbrev TokP := Parser Error.Trivial (Std.Iterators.Types.ArrayIterator Tok) Tok

def num : TokP Nat := tokenMap fun
  | .num n => some n
  | _ => none

def sum : TokP Nat := do
  let ns ← sepBy1 (token Tok.plus) num
  return ns.foldl (· + ·) 0

#eval sum.parseArray #[.num 1, .plus, .num 2, .plus, .num 3] |>.toOption -- some 6
```

`tokenMap f` accepts a token `t` when `f t` is `some x`, and returns `x`.

## Where to go next

* The [`ParseItExamples`](ParseItExamples) directory has complete parsers for BNF, JSON and Roman
  numerals.
* `ParseIt.Char.Unicode` has parsers for Unicode general categories, scripts and other character
  properties, and case-insensitive matching.
* The [source documentation](https://www.dorais.org/lean4-parseit/doc/) describes every combinator.
* Coming from lean4-parser? See [MIGRATION.md](MIGRATION.md).
