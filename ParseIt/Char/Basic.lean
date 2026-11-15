/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ParseIt.Combinators

/-! # Character parsers

Parsers for character tokens. These work with any iterator of `Char`, such as `CharIterator`.
Character classes are ASCII only; Unicode classes are planned separately.
-/

namespace ParseIt.Char
open Std

variable {ε ι : Type} {m : Type → Type} [Iterator ι Id Char] [Iterators.Productive ι Id]
  [Error ε ι Char] [Monad m]

/-- `char c` accepts and returns character `c`. -/
@[inline]
public def char (c : Char) : ParserT ε ι Char m Char :=
  withErrorMessage s!"expected {repr c}" <| token c

/-- `string s` accepts the characters of `s` in order and returns `s`. -/
public def string (s : String) : ParserT ε ι Char m String :=
  withErrorMessage s!"expected {repr s}" do
    for c in s do
      discard <| token c
    return s

/-- Parse space (U+0020). -/
@[inline]
public def space : ParserT ε ι Char m Char :=
  withErrorMessage "expected space (U+0020)" <| token ' '

/-- Parse horizontal tab (U+0009). -/
@[inline]
public def tab : ParserT ε ι Char m Char :=
  withErrorMessage "expected horizontal tab (U+0009)" <| token '\t'

/-- Parse line feed (U+000A). -/
@[inline]
public def ASCII.lf : ParserT ε ι Char m Char :=
  withErrorMessage "expected line feed (U+000A)" <| token '\n'

/-- Parse carriage return (U+000D). -/
@[inline]
public def ASCII.cr : ParserT ε ι Char m Char :=
  withErrorMessage "expected carriage return (U+000D)" <| token '\r'

/-- Parse end of line: line feed, optionally preceded by carriage return. -/
@[inline]
public def eol : ParserT ε ι Char m Char :=
  withErrorMessage "expected newline" <| (ASCII.cr *> ASCII.lf) <|> ASCII.lf

namespace ASCII

/-- Parse whitespace character (space and U+0009 to U+000D). -/
public def whitespace : ParserT ε ι Char m Char :=
  withErrorMessage "expected whitespace character" <|
    tokenFilter fun c => c == ' ' || c >= '\t' && c <= '\r'

/-- Parse uppercase letter character (`A` to `Z`). -/
public def uppercase : ParserT ε ι Char m Char :=
  withErrorMessage "expected uppercase letter character" <|
    tokenFilter fun c => c >= 'A' && c <= 'Z'

/-- Parse lowercase letter character (`a` to `z`). -/
public def lowercase : ParserT ε ι Char m Char :=
  withErrorMessage "expected lowercase letter character" <|
    tokenFilter fun c => c >= 'a' && c <= 'z'

/-- Parse alphabetic character (`A` to `Z` and `a` to `z`). -/
public def alpha : ParserT ε ι Char m Char :=
  withErrorMessage "expected alphabetic character" <|
    tokenFilter fun c => if c >= 'a' then c <= 'z' else c >= 'A' && c <= 'Z'

/-- Parse numeric character (`0` to `9`). -/
public def numeric : ParserT ε ι Char m Char :=
  withErrorMessage "expected decimal digit character" <|
    tokenFilter fun c => c >= '0' && c <= '9'

/-- Parse letter or digit character (`A` to `Z`, `a` to `z` and `0` to `9`). -/
public def alphanum : ParserT ε ι Char m Char :=
  withErrorMessage "expected letter or digit character" <|
    tokenFilter fun c =>
      if c >= 'a' then c <= 'z'
      else if c >= 'A' then c <= 'Z'
      else c >= '0' && c <= '9'

/-- Parse control character (U+0000 to U+001F and U+007F). -/
public def control : ParserT ε ι Char m Char :=
  withErrorMessage "expected control character" <|
    tokenFilter fun c => c.val < 0x20 || c.val == 0x7f

/-- Parse decimal digit (`0` to `9`). -/
public def digit : ParserT ε ι Char m (Fin 10) :=
  withErrorMessage "expected decimal digit" <|
    tokenMap fun c =>
      if c < '0' then none else
        let val := c.toNat - '0'.toNat
        if h : val < 10 then some ⟨val, h⟩ else none

/-- Parse binary digit (`0` or `1`). -/
public def binDigit : ParserT ε ι Char m (Fin 2) :=
  withErrorMessage "expected binary digit" <|
    tokenMap fun
      | '0' => some 0
      | '1' => some 1
      | _ => none

/-- Parse octal digit (`0` to `7`). -/
public def octDigit : ParserT ε ι Char m (Fin 8) :=
  withErrorMessage "expected octal digit" <|
    tokenMap fun c =>
      if c < '0' then none else
        let val := c.toNat - '0'.toNat
        if h : val < 8 then some ⟨val, h⟩ else none

/-- Parse hexadecimal digit (`0` to `9`, `A` to `F` and `a` to `f`). -/
public def hexDigit : ParserT ε ι Char m (Fin 16) :=
  withErrorMessage "expected hexadecimal digit" <|
    tokenMap fun c =>
      if c < '0' then none else
        let val := c.toNat - '0'.toNat
        if h : val < 10 then some ⟨val, by omega⟩
        else if c < 'A' then none else
          let val := val - ('A'.toNat - '9'.toNat - 1)
          if h : val < 16 then some ⟨val, h⟩
          else if c < 'a' then none else
            let val := val - ('a'.toNat - 'A'.toNat)
            if h : val < 16 then some ⟨val, h⟩ else none

end ASCII

end ParseIt.Char
