import ParseIt

open ParseIt Std ScalarArray

namespace ScalarArrayTest

/-- All the elements of the input. -/
def elements (ι τ : Type) [Iterator ι Id τ] [Iterators.Finite ι Id] [HasPos ι τ]
    [LE (HasPos.Pos ι)] [DecidableLE (HasPos.Pos ι)] : Parser (Error.Basic ι) ι τ (Array τ) :=
  takeMany anyToken <* endOfInput

/-- Exactly one element. -/
def single (ι τ : Type) [Iterator ι Id τ] [Iterators.Finite ι Id] [HasPos ι τ]
    [LE (HasPos.Pos ι)] [DecidableLE (HasPos.Pos ι)] : Parser (Error.Basic ι) ι τ τ :=
  anyToken <* endOfInput

/-- The result of a parse, as a string. -/
def show? {ε α : Type} [ToString ε] [ToString α] : Except ε α → String
  | .ok x => s!"ok {x}"
  | .error e => s!"error {e}"

/-! `UInt8Array` -/

-- An array coerces to a slice of all its elements.
#guard show? (Parser.parseUInt8Array (elements UInt8Array.SliceIterator UInt8)
  [1, 2, 3].toUInt8Array) == "ok #[1, 2, 3]"
#guard show? (Parser.parseUInt8Array (elements UInt8Array.SliceIterator UInt8)
  ([1, 2, 3].toUInt8Array[1...2])) == "ok #[2]"
-- Positions are indices in the array, not in the slice.
#guard show? (Parser.parseUInt8Array (single UInt8Array.SliceIterator UInt8)
  ([1, 2, 3].toUInt8Array[1...*])) == "error unexpected input 3 at 2"

/-! `UInt16Array` -/

-- An array coerces to a slice of all its elements.
#guard show? (Parser.parseUInt16Array (elements UInt16Array.SliceIterator UInt16)
  [1, 2, 3].toUInt16Array) == "ok #[1, 2, 3]"
#guard show? (Parser.parseUInt16Array (elements UInt16Array.SliceIterator UInt16)
  ([1, 2, 3].toUInt16Array[1...2])) == "ok #[2]"
-- Positions are indices in the array, not in the slice.
#guard show? (Parser.parseUInt16Array (single UInt16Array.SliceIterator UInt16)
  ([1, 2, 3].toUInt16Array[1...*])) == "error unexpected input 3 at 2"

/-! `UInt32Array` -/

-- An array coerces to a slice of all its elements.
#guard show? (Parser.parseUInt32Array (elements UInt32Array.SliceIterator UInt32)
  [1, 2, 3].toUInt32Array) == "ok #[1, 2, 3]"
#guard show? (Parser.parseUInt32Array (elements UInt32Array.SliceIterator UInt32)
  ([1, 2, 3].toUInt32Array[1...2])) == "ok #[2]"
-- Positions are indices in the array, not in the slice.
#guard show? (Parser.parseUInt32Array (single UInt32Array.SliceIterator UInt32)
  ([1, 2, 3].toUInt32Array[1...*])) == "error unexpected input 3 at 2"

/-! `UInt64Array` -/

-- An array coerces to a slice of all its elements.
#guard show? (Parser.parseUInt64Array (elements UInt64Array.SliceIterator UInt64)
  [1, 2, 3].toUInt64Array) == "ok #[1, 2, 3]"
#guard show? (Parser.parseUInt64Array (elements UInt64Array.SliceIterator UInt64)
  ([1, 2, 3].toUInt64Array[1...2])) == "ok #[2]"
-- Positions are indices in the array, not in the slice.
#guard show? (Parser.parseUInt64Array (single UInt64Array.SliceIterator UInt64)
  ([1, 2, 3].toUInt64Array[1...*])) == "error unexpected input 3 at 2"

/-! `USizeArray` -/

-- An array coerces to a slice of all its elements.
#guard show? (Parser.parseUSizeArray (elements USizeArray.SliceIterator USize)
  [1, 2, 3].toUSizeArray) == "ok #[1, 2, 3]"
#guard show? (Parser.parseUSizeArray (elements USizeArray.SliceIterator USize)
  ([1, 2, 3].toUSizeArray[1...2])) == "ok #[2]"
-- Positions are indices in the array, not in the slice.
#guard show? (Parser.parseUSizeArray (single USizeArray.SliceIterator USize)
  ([1, 2, 3].toUSizeArray[1...*])) == "error unexpected input 3 at 2"

/-! `Int8Array` -/

-- An array coerces to a slice of all its elements.
#guard show? (Parser.parseInt8Array (elements Int8Array.SliceIterator Int8)
  [1, -2, 3].toInt8Array) == "ok #[1, -2, 3]"
#guard show? (Parser.parseInt8Array (elements Int8Array.SliceIterator Int8)
  ([1, -2, 3].toInt8Array[1...2])) == "ok #[-2]"
-- Positions are indices in the array, not in the slice.
#guard show? (Parser.parseInt8Array (single Int8Array.SliceIterator Int8)
  ([1, -2, 3].toInt8Array[1...*])) == "error unexpected input 3 at 2"

/-! `Int16Array` -/

-- An array coerces to a slice of all its elements.
#guard show? (Parser.parseInt16Array (elements Int16Array.SliceIterator Int16)
  [1, -2, 3].toInt16Array) == "ok #[1, -2, 3]"
#guard show? (Parser.parseInt16Array (elements Int16Array.SliceIterator Int16)
  ([1, -2, 3].toInt16Array[1...2])) == "ok #[-2]"
-- Positions are indices in the array, not in the slice.
#guard show? (Parser.parseInt16Array (single Int16Array.SliceIterator Int16)
  ([1, -2, 3].toInt16Array[1...*])) == "error unexpected input 3 at 2"

/-! `Int32Array` -/

-- An array coerces to a slice of all its elements.
#guard show? (Parser.parseInt32Array (elements Int32Array.SliceIterator Int32)
  [1, -2, 3].toInt32Array) == "ok #[1, -2, 3]"
#guard show? (Parser.parseInt32Array (elements Int32Array.SliceIterator Int32)
  ([1, -2, 3].toInt32Array[1...2])) == "ok #[-2]"
-- Positions are indices in the array, not in the slice.
#guard show? (Parser.parseInt32Array (single Int32Array.SliceIterator Int32)
  ([1, -2, 3].toInt32Array[1...*])) == "error unexpected input 3 at 2"

/-! `Int64Array` -/

-- An array coerces to a slice of all its elements.
#guard show? (Parser.parseInt64Array (elements Int64Array.SliceIterator Int64)
  [1, -2, 3].toInt64Array) == "ok #[1, -2, 3]"
#guard show? (Parser.parseInt64Array (elements Int64Array.SliceIterator Int64)
  ([1, -2, 3].toInt64Array[1...2])) == "ok #[-2]"
-- Positions are indices in the array, not in the slice.
#guard show? (Parser.parseInt64Array (single Int64Array.SliceIterator Int64)
  ([1, -2, 3].toInt64Array[1...*])) == "error unexpected input 3 at 2"

/-! `ISizeArray` -/

-- An array coerces to a slice of all its elements.
#guard show? (Parser.parseISizeArray (elements ISizeArray.SliceIterator ISize)
  [1, -2, 3].toISizeArray) == "ok #[1, -2, 3]"
#guard show? (Parser.parseISizeArray (elements ISizeArray.SliceIterator ISize)
  ([1, -2, 3].toISizeArray[1...2])) == "ok #[-2]"
-- Positions are indices in the array, not in the slice.
#guard show? (Parser.parseISizeArray (single ISizeArray.SliceIterator ISize)
  ([1, -2, 3].toISizeArray[1...*])) == "error unexpected input 3 at 2"

/-! `Float32Array` -/

-- An array coerces to a slice of all its elements.
#guard show? (Parser.parseFloat32Array (elements Float32Array.SliceIterator Float32)
  [1, -2, 3].toFloat32Array) == "ok #[1.000000, -2.000000, 3.000000]"
#guard show? (Parser.parseFloat32Array (elements Float32Array.SliceIterator Float32)
  ([1, -2, 3].toFloat32Array[1...2])) == "ok #[-2.000000]"
-- Positions are indices in the array, not in the slice.
#guard show? (Parser.parseFloat32Array (single Float32Array.SliceIterator Float32)
  ([1, -2, 3].toFloat32Array[1...*])) == "error unexpected input 3.000000 at 2"

/-! `Float64Array` -/

-- An array coerces to a slice of all its elements.
#guard show? (Parser.parseFloat64Array (elements Float64Array.SliceIterator Float)
  [1, -2, 3].toFloat64Array) == "ok #[1.000000, -2.000000, 3.000000]"
#guard show? (Parser.parseFloat64Array (elements Float64Array.SliceIterator Float)
  ([1, -2, 3].toFloat64Array[1...2])) == "ok #[-2.000000]"
-- Positions are indices in the array, not in the slice.
#guard show? (Parser.parseFloat64Array (single Float64Array.SliceIterator Float)
  ([1, -2, 3].toFloat64Array[1...*])) == "error unexpected input 3.000000 at 2"

/-! `FloatArray` -/

#guard show? (Parser.parseFloatArray (elements Float64Array.SliceIterator Float)
  (FloatArray.mk #[1, -2, 3])) == "ok #[1.000000, -2.000000, 3.000000]"
#guard show? (Parser.parseFloatArray (single Float64Array.SliceIterator Float)
  (FloatArray.mk #[1, -2])) == "error unexpected input -2.000000 at 1"
#guard show? (Parser.parseFloatArray (elements Float64Array.SliceIterator Float)
  (FloatArray.mk #[])) == "ok #[]"

end ScalarArrayTest
