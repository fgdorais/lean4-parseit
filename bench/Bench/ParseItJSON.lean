/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

-- Ported from `examples/JSON.lean` in https://github.com/fgdorais/lean4-parser

import ParseIt

/-! # A JSON validator

The JSON data interchange syntax is defined in [ECMA Standard 404][ECMA]. A convenient visual
representation of the syntax can be found at [json.org][JSON].

The value parsers are mutually recursive, so they are `partial`. The repetitions inside them are
total, as everywhere in ParseIt.

[ECMA]: https://www.ecma-international.org/publications-and-standards/standards/ecma-404/
[JSON]: https://www.json.org/json-en.html
-/

namespace BenchParseIt.JSON

open ParseIt ParseIt.Char

/-- JSON parser monad. -/
protected abbrev Parser := ParseIt.Parser (Error.Simple CharIterator) CharIterator Char

instance {α} : Inhabited (BenchParseIt.JSON.Parser α) := ⟨throwUnexpected⟩

/--
Parse JSON white space: space (U+0020), line feed (U+000A), carriage return (U+000D) and horizontal
tab (U+0009).
```
<ws> ::= "" | U+0020 <ws> | U+000A <ws> | U+000D <ws> | U+0009 <ws>
```
-/
def ws : BenchParseIt.JSON.Parser Unit :=
  dropMany <| tokenFilter [' ', '\n', '\r', '\t'].contains

/--
Parse a JSON number.
```
<number> ::= <integer> <optional-fraction> <optional-exponent>
<integer> ::= <optional-negative> "0" | <optional-negative> <positive-digit> <digits>
<optional-fraction> ::= "" | "." <digit> <digits>
<optional-exponent> ::= "" | <exp> <optional-sign> <digit> <digits>
```
-/
protected def number : BenchParseIt.JSON.Parser Unit :=
  withErrorMessage "expected number" do
    optional (char '-')
    first [drop 1 (char '0'), dropMany1 ASCII.digit]
    optional do
      drop 1 (char '.')
      dropMany1 ASCII.digit
    optional do
      drop 1 (char 'e' <|> char 'E')
      optional (char '+' <|> char '-')
      dropMany1 ASCII.digit

/--
Parse a JSON string.
```
<string> ::= """" <characters> """"
<character> ::= "\" <escape> | U+0020 .. U+10FFFF except """" (U+0022) and "\" (U+005C)
<escape> ::= """" | "\" | "/" | "b" | "f" | "n" | "r" | "t"
    | "u" <hex-digit> <hex-digit> <hex-digit> <hex-digit>
```
-/
protected def string : BenchParseIt.JSON.Parser Unit :=
  withErrorMessage "expected string" do
    char '"' *> dropUntil (drop 1 <| char '"') do
      first [
        char '\\' *> escape,
        drop 1 <| tokenFilter fun c => c ≥ ' ' && c != '"' && c != '\\']
where
  escape : BenchParseIt.JSON.Parser Unit :=
    withErrorMessage "expected escape" do
      first [
        drop 1 <| tokenFilter ['"', '\\', '/', 'b', 'f', 'n', 'r', 't'].contains,
        char 'u' *> drop 4 ASCII.hexDigit]

mutual

/--
Parse a JSON value.
```
<value> ::= <object> | <array> | <string> | <number> | "true" | "false" | "null"
```
-/
protected partial def value : BenchParseIt.JSON.Parser Unit :=
  first [
    BenchParseIt.JSON.object,
    BenchParseIt.JSON.array,
    BenchParseIt.JSON.string,
    BenchParseIt.JSON.number,
    drop 1 <| string "true",
    drop 1 <| string "false",
    drop 1 <| string "null"]

/--
Parse a JSON object.
```
<object> ::= "{" <ws> "}" | "{" <members> "}"
<members> ::= <member> | <member> "," <members>
<member> ::= <ws> <string> <ws> ":" <ws> <value> <ws>
```
-/
protected partial def object : BenchParseIt.JSON.Parser Unit :=
  withErrorMessage "expected object" do
    drop 1 <| char '{'
    ws
    discard <| sepBy (char ',') do
      ws *> BenchParseIt.JSON.string <* ws
      drop 1 <| char ':'
      ws *> BenchParseIt.JSON.value <* ws
    drop 1 <| char '}'

/--
Parse a JSON array.
```
<array> ::= "[" <ws> "]" | "[" <elements> "]"
<elements> ::= <element> | <element> "," <elements>
<element> ::= <ws> <value> <ws>
```
-/
protected partial def array : BenchParseIt.JSON.Parser Unit :=
  withErrorMessage "expected array" do
    drop 1 <| char '['
    ws
    discard <| sepBy (char ',') (ws *> BenchParseIt.JSON.value <* ws)
    drop 1 <| char ']'

end

/-- JSON validator. -/
def validate (s : String) : Bool :=
  match (ws *> BenchParseIt.JSON.value <* ws <* endOfInput).parseString s with
  | .ok _ => true
  | .error _ => false

end BenchParseIt.JSON
