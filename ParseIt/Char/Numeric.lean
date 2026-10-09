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

/-- Fold decimal digits into `n`, returning the value and the number of digits. -/
@[inline]
private def decNum (n : Nat := 0) : ParserT ε ι Char m (Nat × Nat) :=
  foldl (fun (r : Nat × Nat) (d : Fin 10) => (10 * r.1 + d, r.2 + 1)) (n, 0) digit

/-- Fold binary digits into `n`, returning the value and the number of digits. -/
@[inline]
private def binNum (n : Nat := 0) : ParserT ε ι Char m (Nat × Nat) :=
  foldl (fun (r : Nat × Nat) (d : Fin 2) => (r.1 <<< 1 + d, r.2 + 1)) (n, 0) binDigit

/-- Fold octal digits into `n`, returning the value and the number of digits. -/
@[inline]
private def octNum (n : Nat := 0) : ParserT ε ι Char m (Nat × Nat) :=
  foldl (fun (r : Nat × Nat) (d : Fin 8) => (r.1 <<< 3 + d, r.2 + 1)) (n, 0) octDigit

/-- Fold hexadecimal digits into `n`, returning the value and the number of digits. -/
@[inline]
private def hexNum (n : Nat := 0) : ParserT ε ι Char m (Nat × Nat) :=
  foldl (fun (r : Nat × Nat) (d : Fin 16) => (r.1 <<< 4 + d, r.2 + 1)) (n, 0) hexDigit

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
