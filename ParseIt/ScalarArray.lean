/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ParseIt.Input
public import ScalarArray

/-! # Scalar array inputs

Parsers over the elements of the arrays of
[lean4-scalar-arrays](https://github.com/fgdorais/lean4-scalar-arrays): `HasPos` instances for
their slice iterators, and a runner named after each array type, such as `parseUInt8Array` for
`UInt8Array`. A runner also takes a slice of the array; an array coerces to a slice of all its
elements. Positions are indices in the underlying array, not in the slice. `Parser.parseSlice`
remains the runner for `String.Slice`.

These arrays are named `UInt8Array` and `Float64Array` because core has `ByteArray` and
`FloatArray`. `parseFloatArray` uses the same iterator as `parseFloat64Array`, so a parser for one
runs on the other. `parseByteArray` uses `ByteIterator` instead, so only a parser that is
polymorphic in the iterator runs on both it and `parseUInt8Array`.
-/

namespace ParseIt
open Std ScalarArray

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

/-- Positions are indices in the underlying array. -/
public instance : HasPos UInt64Array.SliceIterator UInt64 where
  Pos := Nat
  pos it := it.toUInt64Slice.start

/-- Positions are indices in the underlying array. -/
public instance : HasPos USizeArray.SliceIterator USize where
  Pos := Nat
  pos it := it.toUSizeSlice.start

/-- Positions are indices in the underlying array. -/
public instance : HasPos Int8Array.SliceIterator Int8 where
  Pos := Nat
  pos it := it.toInt8Slice.start

/-- Positions are indices in the underlying array. -/
public instance : HasPos Int16Array.SliceIterator Int16 where
  Pos := Nat
  pos it := it.toInt16Slice.start

/-- Positions are indices in the underlying array. -/
public instance : HasPos Int32Array.SliceIterator Int32 where
  Pos := Nat
  pos it := it.toInt32Slice.start

/-- Positions are indices in the underlying array. -/
public instance : HasPos Int64Array.SliceIterator Int64 where
  Pos := Nat
  pos it := it.toInt64Slice.start

/-- Positions are indices in the underlying array. -/
public instance : HasPos ISizeArray.SliceIterator ISize where
  Pos := Nat
  pos it := it.toISizeSlice.start

/-- Positions are indices in the underlying array. -/
public instance : HasPos Float32Array.SliceIterator Float32 where
  Pos := Nat
  pos it := it.toFloat32Slice.start

/-- Positions are indices in the underlying array. -/
public instance : HasPos Float64Array.SliceIterator Float where
  Pos := Nat
  pos it := it.toFloatSlice.start

namespace Parser
variable {ε α : Type}

/-- Run `p` on the elements of `s`, an array or a slice of one. Positions are indices in the
array. -/
@[inline]
public def parseUInt8Array (p : Parser ε UInt8Array.SliceIterator UInt8 α)
    (s : UInt8Array.Slice) : Except ε α :=
  p.parse s.iter

/-- Run `p` on the elements of `s`, an array or a slice of one. Positions are indices in the
array. -/
@[inline]
public def parseUInt16Array (p : Parser ε UInt16Array.SliceIterator UInt16 α)
    (s : UInt16Array.Slice) : Except ε α :=
  p.parse s.iter

/-- Run `p` on the elements of `s`, an array or a slice of one. Positions are indices in the
array. -/
@[inline]
public def parseUInt32Array (p : Parser ε UInt32Array.SliceIterator UInt32 α)
    (s : UInt32Array.Slice) : Except ε α :=
  p.parse s.iter

/-- Run `p` on the elements of `s`, an array or a slice of one. Positions are indices in the
array. -/
@[inline]
public def parseUInt64Array (p : Parser ε UInt64Array.SliceIterator UInt64 α)
    (s : UInt64Array.Slice) : Except ε α :=
  p.parse s.iter

/-- Run `p` on the elements of `s`, an array or a slice of one. Positions are indices in the
array. -/
@[inline]
public def parseUSizeArray (p : Parser ε USizeArray.SliceIterator USize α)
    (s : USizeArray.Slice) : Except ε α :=
  p.parse s.iter

/-- Run `p` on the elements of `s`, an array or a slice of one. Positions are indices in the
array. -/
@[inline]
public def parseInt8Array (p : Parser ε Int8Array.SliceIterator Int8 α)
    (s : Int8Array.Slice) : Except ε α :=
  p.parse s.iter

/-- Run `p` on the elements of `s`, an array or a slice of one. Positions are indices in the
array. -/
@[inline]
public def parseInt16Array (p : Parser ε Int16Array.SliceIterator Int16 α)
    (s : Int16Array.Slice) : Except ε α :=
  p.parse s.iter

/-- Run `p` on the elements of `s`, an array or a slice of one. Positions are indices in the
array. -/
@[inline]
public def parseInt32Array (p : Parser ε Int32Array.SliceIterator Int32 α)
    (s : Int32Array.Slice) : Except ε α :=
  p.parse s.iter

/-- Run `p` on the elements of `s`, an array or a slice of one. Positions are indices in the
array. -/
@[inline]
public def parseInt64Array (p : Parser ε Int64Array.SliceIterator Int64 α)
    (s : Int64Array.Slice) : Except ε α :=
  p.parse s.iter

/-- Run `p` on the elements of `s`, an array or a slice of one. Positions are indices in the
array. -/
@[inline]
public def parseISizeArray (p : Parser ε ISizeArray.SliceIterator ISize α)
    (s : ISizeArray.Slice) : Except ε α :=
  p.parse s.iter

/-- Run `p` on the elements of `s`, an array or a slice of one. Positions are indices in the
array. -/
@[inline]
public def parseFloat32Array (p : Parser ε Float32Array.SliceIterator Float32 α)
    (s : Float32Array.Slice) : Except ε α :=
  p.parse s.iter

/-- Run `p` on the elements of `s`, an array or a slice of one. Positions are indices in the
array. -/
@[inline]
public def parseFloat64Array (p : Parser ε Float64Array.SliceIterator Float α)
    (s : Float64Array.Slice) : Except ε α :=
  p.parse s.iter

/-- Run `p` on the elements of `xs`. Positions are array indices. -/
@[inline]
public def parseFloatArray (p : Parser ε Float64Array.SliceIterator Float α) (xs : FloatArray) :
    Except ε α :=
  p.parse xs.toFloat64Array.iter

end Parser

end ParseIt
