/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ParseIt.Char.Basic

/-! # Numeric parsers

ASCII parsers for natural numbers, integers and scientific notation.
-/

namespace ParseIt.Char.ASCII
open Std

variable {ε ι : Type} {m : Type → Type} [Iterator ι Id Char] [Iterators.Finite ι Id]
  [Error ε ι Char] [Monad m]

/--
Digits read so far in some base: the full chunks of a fixed number of digits, then the `len`
digits of `cur`. Chunks stay small enough to avoid bignum arithmetic until they are combined.
-/
private structure Digits where
  /-- Values of the full chunks, most significant first. -/
  chunks : Array Nat := #[]
  /-- Value of the digits after the last full chunk. -/
  cur : Nat := 0
  /-- Number of digits after the last full chunk. -/
  len : UInt8 := 0

namespace Digits

/-- Add digit `d` in base `b`, starting a new chunk after `size` digits. -/
@[inline]
private def push (b : Nat) (size : UInt8) (s : Digits) (d : Nat) : Digits :=
  if s.len < size then { s with cur := b * s.cur + d, len := s.len + 1 }
  else { chunks := s.chunks.push s.cur, cur := d, len := 1 }

/--
Value of `chunks[lo:hi]`, each chunk having `size` digits, where `shift x k` appends `k` zero
digits to `x`. Splitting in halves lets bignum multiplication do the work in subquadratic time.
-/
@[specialize]
private def combine (shift : Nat → Nat → Nat) (size : Nat) (chunks : Array Nat) (lo hi : Nat) :
    Nat :=
  if hi ≤ lo then 0
  else if hi = lo + 1 then chunks[lo]?.getD 0
  else
    let mid := (lo + hi) / 2
    shift (combine shift size chunks lo mid) (size * (hi - mid)) +
      combine shift size chunks mid hi
termination_by hi - lo

end Digits

/--
Fold the digits parsed by `digit` into `n`, returning the value and the number of digits. Digits
are read in chunks of `size` and `shift x k` appends `k` zero digits to `x`.
-/
@[inline]
private def numDigits {b : Nat} (size : Nat) (shift : Nat → Nat → Nat)
    (digit : ParserT ε ι Char m (Fin b)) (n : Nat) : ParserT ε ι Char m (Nat × Nat) := do
  -- `n` sits in front of the first chunk, which is correct since chunks are weighted by position
  let s ← foldl (fun (s : Digits) (d : Fin b) => s.push b size.toUInt8 d) { cur := n } digit
  let k := s.chunks.size * size + s.len.toNat
  if s.chunks.isEmpty then return (s.cur, k)
  let v := Digits.combine shift size s.chunks 0 s.chunks.size
  return (shift v s.len.toNat + s.cur, k)

/-- Fold decimal digits into `n`, returning the value and the number of digits. -/
@[inline]
private def decNum (n : Nat := 0) : ParserT ε ι Char m (Nat × Nat) :=
  numDigits 18 (fun x k => x * 10 ^ k) digit n

/-- Fold binary digits into `n`, returning the value and the number of digits. -/
@[inline]
private def binNum (n : Nat := 0) : ParserT ε ι Char m (Nat × Nat) :=
  numDigits 62 (fun x k => x <<< k) binDigit n

/-- Fold octal digits into `n`, returning the value and the number of digits. -/
@[inline]
private def octNum (n : Nat := 0) : ParserT ε ι Char m (Nat × Nat) :=
  numDigits 20 (fun x k => x <<< (3 * k)) octDigit n

/-- Fold hexadecimal digits into `n`, returning the value and the number of digits. -/
@[inline]
private def hexNum (n : Nat := 0) : ParserT ε ι Char m (Nat × Nat) :=
  numDigits 15 (fun x k => x <<< (4 * k)) hexDigit n

/--
Parse a `Nat`. Unless `decimalOnly` is `true`, a leading `0` introduces binary (`0b`), hexadecimal
(`0x`) or octal digits.
-/
public def parseNat (decimalOnly := true) : ParserT ε ι Char m Nat := do
  match ← digit with
  | ⟨0, _⟩ =>
    if decimalOnly then
      Prod.fst <$> decNum
    else
      first [
        char 'b' *> (binDigit >>= fun d => Prod.fst <$> binNum d),
        char 'x' *> (hexDigit >>= fun d => Prod.fst <$> hexNum d),
        octDigit >>= fun d => Prod.fst <$> octNum d,
        pure 0]
  | ⟨n, _⟩ => Prod.fst <$> decNum n

/-- Parse an `Int`, with an optional sign. -/
public def parseInt (decimalOnly := true) : ParserT ε ι Char m Int := do
  match ← option? (char '+' <|> char '-') with
  | some '-' => Int.negOfNat <$> parseNat decimalOnly
  | _ => Int.ofNat <$> parseNat decimalOnly

/-- Parse an unsigned number in scientific notation. -/
public def parseScientific (α) [OfScientific α] : ParserT ε ι Char m α := do
  let (man, pre) ← decNum
  let (man, aft) ← (char '.' *> decNum man) <|> pure (man, 0)
  if pre + aft = 0 then throwUnexpected
  let exp : Int ← ((char 'E' <|> char 'e') *> parseInt) <|> pure 0
  return OfScientific.ofScientific man (exp < aft) (exp - aft).natAbs

/-- Parse a `Float`, with an optional sign. -/
public def parseFloat : ParserT ε ι Char m Float := do
  match ← option? (char '+' <|> char '-') with
  | some '-' => Float.neg <$> parseScientific Float
  | _ => parseScientific Float

end ParseIt.Char.ASCII
