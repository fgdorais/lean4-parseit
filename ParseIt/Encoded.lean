/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ParseIt.Input
public import UnicodeFormat

/-! # Encoded inputs

Parsers over the characters of UTF-8, UTF-16 and UTF-32 input, using the decoding iterators of
[UnicodeFormat](https://github.com/fgdorais/lean4-unicode-format). Positions are those of the
encoded input: byte offsets for UTF-8, and code unit indices for UTF-16 and UTF-32.

A strict decoding iterator ends at the first ill-formed input, so a parser sees the end of the
input there. `Parser.parseDecoded` and the `parseUTF8`, `parseUTF16` and `parseUTF32` runners
report the ill-formed input as an error when the parser stops where decoding stopped, or fails
there.
-/

namespace ParseIt
open Std Unicode ScalarArray

/-- Positions are indices in the underlying array. -/
public instance : HasPos UInt8Array.SliceIterator UInt8 where
  Pos := Nat
  pos it := it.toUInt8Slice.start

/-- Positions are indices in the underlying array. -/
public instance : HasPos UInt16Array.SliceIterator UInt16 where
  Pos := Nat
  pos it := it.toUInt16Slice.start

/-- Positions are indices in the underlying array. -/
public instance : HasPos UInt32Array.SliceIterator UInt32 where
  Pos := Nat
  pos it := it.toUInt32Slice.start

/-- Positions are those of the input iterator, at the start of the next token to decode. -/
public instance {δ ι τ σ : Type} [Decoder δ τ σ] [Iterator ι Id τ] [Iterators.Productive ι Id]
    [HasPos ι τ] : HasPos (DecodeIterator δ ι) σ where
  Pos := HasPos.Pos ι
  pos it := HasPos.pos it.decodeBase

/-- The iterator over the characters of UTF-8 bytes. -/
public abbrev UTF8Iterator : Type := DecodeIterator UTF8 UInt8Array.SliceIterator

/-- The iterator over the characters of UTF-16 code units. -/
public abbrev UTF16Iterator : Type := DecodeIterator UTF16 UInt16Array.SliceIterator

/-- The iterator over the characters of UTF-32 code units. -/
public abbrev UTF32Iterator : Type := DecodeIterator UTF32 UInt32Array.SliceIterator

namespace Parser
variable {ε δ ι τ α : Type}

/--
`p.parseDecoded it` runs `p` on the characters of the decoding iterator `it`. When `it` is strict
and stops at ill-formed input, that input is reported as an error, at its position, if `p` stops
there or fails there. When `p` fails before, its error is merged with that of the ill-formed input,
so with the furthest position rule of `Error.Basic` the error of `p` is reported.
-/
public def parseDecoded [Decoder δ τ Char] [Iterator ι Id τ] [Iterators.Finite ι Id]
    [Error ε (DecodeIterator δ ι) Char] (p : Parser ε (DecodeIterator δ ι) Char α)
    (it : Iter (α := DecodeIterator δ ι) Char) : Except ε α :=
  let ill (it : Iter (α := DecodeIterator δ ι) Char) (k : DecodeError.Kind) : ε :=
    Error.addMessage (Error.unexpected it none) it (toString k)
  match p.run it with
  | .ok rest _ x =>
    match if rest.decodeIsLossy then none else rest.decodeError? with
    | none => .ok x
    | some k => .error (ill rest k)
  | .error e =>
    if it.decodeIsLossy then .error e
    else
      match it.decodeFailure? with
      | some (k, bad) => .error (Error.merge (ι := DecodeIterator δ ι) e (ill bad k))
      | none => .error e

/-- Run `p` on the characters of the UTF-8 bytes `b`, reporting ill-formed bytes as errors.
Positions are byte offsets. -/
@[inline]
public def parseUTF8 [Error ε UTF8Iterator Char] (p : Parser ε UTF8Iterator Char α)
    (b : ByteArray) : Except ε α :=
  p.parseDecoded (UTF8.decodeIter b.toUInt8Array.iter)

/-- Run `p` on the characters of the UTF-16 code units `s`, reporting unpaired surrogates as
errors. Positions are indices in the array of `s`. -/
@[inline]
public def parseUTF16 [Error ε UTF16Iterator Char] (p : Parser ε UTF16Iterator Char α)
    (s : UInt16Array.Slice) : Except ε α :=
  p.parseDecoded (UTF16.decodeIter s.iter)

/-- Run `p` on the characters of the UTF-32 code units `s`, reporting code units that are not
scalar values as errors. Positions are indices in the array of `s`. -/
@[inline]
public def parseUTF32 [Error ε UTF32Iterator Char] (p : Parser ε UTF32Iterator Char α)
    (s : UInt32Array.Slice) : Except ε α :=
  p.parseDecoded (UTF32.decodeIter s.iter)

end Parser

end ParseIt
