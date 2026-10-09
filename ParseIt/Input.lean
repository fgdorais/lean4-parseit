/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ParseIt.Basic
public import ParseIt.Combinators
public import Std.Data.Iterators

/-! # Parser inputs

Iterators for common parser inputs, with `HasPos` instances for error reporting:

* `CharIterator` iterates over the characters of a `String.Slice`. Unlike `String.Slice.chars`,
  its type does not depend on the slice, so parsers can name it.
* `ByteIterator` iterates over the bytes of a `ByteArray`.
* `BitIterator` iterates over the bits of a `BitVec`, least significant bit first.
* Core's `ArrayIterator` (from `Array.iter`) reports its index as the position.
-/

namespace ParseIt
open Std

/-- Iterator over the characters of a `String.Slice`. -/
public structure CharIterator where
  /-- The slice being iterated over. -/
  slice : String.Slice
  /-- The current position in `slice`. -/
  pos : slice.Pos

namespace CharIterator

public instance : Iterator CharIterator Id Char where
  IsPlausibleStep it
    | .yield it' c =>
      ∃ h : it.internalState.pos ≠ it.internalState.slice.endPos,
        it'.internalState = ⟨it.internalState.slice, it.internalState.pos.next h⟩ ∧
        c = it.internalState.pos.get h
    | .skip _ => False
    | .done => it.internalState.pos = it.internalState.slice.endPos
  step := fun ⟨⟨s, pos⟩⟩ =>
    if h : pos = s.endPos then
      pure (.deflate ⟨.done, h⟩)
    else
      pure (.deflate ⟨.yield ⟨⟨s, pos.next h⟩⟩ (pos.get h), ⟨h, rfl, rfl⟩⟩)

private def finitenessRelation : Iterators.FinitenessRelation CharIterator Id where
  Rel := InvImage WellFoundedRelation.rel
    (fun it => it.internalState.slice.utf8ByteSize - it.internalState.pos.offset.byteIdx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨h1, h2, _⟩ := h'
      rw [h2]
      have h3 := Char.utf8Size_pos (it.internalState.pos.get h1)
      have h4 := (it.internalState.pos.next h1).isValidForSlice.le_utf8ByteSize
      simp [String.Slice.Pos.ext_iff, String.Pos.Raw.ext_iff] at h1 h4 ⊢
      omega
    · cases h'
    · cases h

public instance : Iterators.Finite CharIterator Id :=
  .of_finitenessRelation finitenessRelation

/-- Positions are byte offsets into the slice. -/
public instance : HasPos CharIterator Char where
  Pos := String.Pos.Raw
  pos it := it.internalState.pos.offset

/-- Iterator over the characters of `s`. -/
@[inline]
public def ofSlice (s : String.Slice) : Iter (α := CharIterator) Char :=
  ⟨⟨s, s.startPos⟩⟩

/-- The remaining characters as a slice. -/
@[inline]
public def remaining (it : Iter (α := CharIterator) Char) : String.Slice :=
  it.internalState.slice.sliceFrom it.internalState.pos

end CharIterator

/-- Iterator over the bytes of a `ByteArray`. -/
public structure ByteIterator where
  /-- The bytes being iterated over. -/
  data : ByteArray
  /-- The current index in `data`. -/
  pos : Nat

namespace ByteIterator

public instance : Iterator ByteIterator Id UInt8 where
  IsPlausibleStep it
    | .yield it' b =>
      ∃ h : it.internalState.pos < it.internalState.data.size,
        it'.internalState = ⟨it.internalState.data, it.internalState.pos + 1⟩ ∧
        b = it.internalState.data[it.internalState.pos]
    | .skip _ => False
    | .done => ¬ it.internalState.pos < it.internalState.data.size
  step := fun ⟨⟨data, pos⟩⟩ =>
    if h : pos < data.size then
      pure (.deflate ⟨.yield ⟨⟨data, pos + 1⟩⟩ data[pos], ⟨h, rfl, rfl⟩⟩)
    else
      pure (.deflate ⟨.done, h⟩)

private def finitenessRelation : Iterators.FinitenessRelation ByteIterator Id where
  Rel := InvImage WellFoundedRelation.rel
    (fun it => it.internalState.data.size - it.internalState.pos)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨h1, h2, _⟩ := h'
      rw [h2]
      dsimp only
      omega
    · cases h'
    · cases h

public instance : Iterators.Finite ByteIterator Id :=
  .of_finitenessRelation finitenessRelation

/-- Positions are byte indices. -/
public instance : HasPos ByteIterator UInt8 where
  Pos := Nat
  pos it := it.internalState.pos

/-- Iterator over the bytes of `data`. -/
@[inline]
public def ofByteArray (data : ByteArray) : Iter (α := ByteIterator) UInt8 :=
  ⟨⟨data, 0⟩⟩

end ByteIterator

/-- Iterator over the bits of a `BitVec`, least significant bit first. -/
public structure BitIterator where
  /-- The width of `bits`. -/
  width : Nat
  /-- The bits being iterated over. -/
  bits : BitVec width
  /-- The index of the current bit. -/
  pos : Nat

namespace BitIterator

public instance : Iterator BitIterator Id Bool where
  IsPlausibleStep it
    | .yield it' b =>
      ∃ h : it.internalState.pos < it.internalState.width,
        it'.internalState = ⟨_, it.internalState.bits, it.internalState.pos + 1⟩ ∧
        b = it.internalState.bits[it.internalState.pos]
    | .skip _ => False
    | .done => ¬ it.internalState.pos < it.internalState.width
  step := fun ⟨⟨width, bits, pos⟩⟩ =>
    if h : pos < width then
      pure (.deflate ⟨.yield ⟨⟨width, bits, pos + 1⟩⟩ bits[pos], ⟨h, rfl, rfl⟩⟩)
    else
      pure (.deflate ⟨.done, h⟩)

private def finitenessRelation : Iterators.FinitenessRelation BitIterator Id where
  Rel := InvImage WellFoundedRelation.rel
    (fun it => it.internalState.width - it.internalState.pos)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨h1, h2, _⟩ := h'
      rw [h2]
      dsimp only
      omega
    · cases h'
    · cases h

public instance : Iterators.Finite BitIterator Id :=
  .of_finitenessRelation finitenessRelation

/-- Positions are bit indices. -/
public instance : HasPos BitIterator Bool where
  Pos := Nat
  pos it := it.internalState.pos

/-- Iterator over the bits of `bits`, least significant bit first. -/
@[inline]
public def ofBitVec {w : Nat} (bits : BitVec w) : Iter (α := BitIterator) Bool :=
  ⟨⟨w, bits, 0⟩⟩

end BitIterator

/-- Positions are array indices. -/
public instance {α : Type} : HasPos (Iterators.Types.ArrayIterator α) α where
  Pos := Nat
  pos it := it.internalState.pos

/-! # Running parsers -/

/--
`captureSlice p` parses `p` and returns its result together with the slice of input that `p`
consumed. The slice is a view into the input; no characters are copied.
-/
public def captureSlice {ε α : Type} {m : Type → Type} [Monad m]
    (p : ParserT ε CharIterator Char m α) : ParserT ε CharIterator Char m (α × String.Slice) :=
  fun it => do
    match ← p it with
    | .ok rest h x =>
      let s := it.internalState.slice
      let stop := s.pos! rest.internalState.pos.offset
      return .ok rest h (x, s.slice! it.internalState.pos stop)
    | .error e => return .error e

namespace Parser
variable {ε τ α : Type}

/-- Run `p` on the characters of `s`. -/
@[inline]
public def parseSlice (p : Parser ε CharIterator Char α) (s : String.Slice) : Except ε α :=
  p.parse (CharIterator.ofSlice s)

/-- Run `p` on the characters of `s`. -/
@[inline]
public def parseString (p : Parser ε CharIterator Char α) (s : String) : Except ε α :=
  p.parseSlice s.toSlice

/-- Run `p` on the bytes of `data`. -/
@[inline]
public def parseByteArray (p : Parser ε ByteIterator UInt8 α) (data : ByteArray) :
    Except ε α :=
  p.parse (ByteIterator.ofByteArray data)

/-- Run `p` on the bits of `bits`, least significant bit first. -/
@[inline]
public def parseBitVec {w : Nat} (p : Parser ε BitIterator Bool α) (bits : BitVec w) :
    Except ε α :=
  p.parse (BitIterator.ofBitVec bits)

/-- Run `p` on the elements of `xs`. -/
@[inline]
public def parseArray (p : Parser ε (Iterators.Types.ArrayIterator τ) τ α) (xs : Array τ) :
    Except ε α :=
  p.parse xs.iter

/-- Run `p` on the elements of `xs`. Vectors use the array iterator. -/
@[inline]
public def parseVector {n : Nat} (p : Parser ε (Iterators.Types.ArrayIterator τ) τ α)
    (xs : Vector τ n) : Except ε α :=
  p.parse xs.iter

/-- Run `p` on the elements of `xs`. Lists have no `HasPos` instance. -/
@[inline]
public def parseList (p : Parser ε (Iterators.Types.ListIterator τ) τ α) (xs : List τ) :
    Except ε α :=
  p.parse xs.iter

end Parser

end ParseIt
