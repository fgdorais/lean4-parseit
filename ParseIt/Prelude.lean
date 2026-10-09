/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-! # Prelude: universe polymorphic basic types

Parsers in `Type u` return results in `Type u`, so combinators that would return `Unit`, `Bool` or
`Nat` return `Unitᵤ`, `Boolᵤ` or `Natᵤ` instead. These coerce to `Bool` and `Nat`, and
their `Repr` instances print the same as `Bool` and `Nat`.
-/

universe u

namespace ParseIt

/-- `Unit` in any universe. -/
public abbrev Unitᵤ : Type u := PUnit

/-- `Bool` in any universe. -/
public inductive Boolᵤ : Type u where
  /-- False. -/
  | false
  /-- True. -/
  | true
deriving DecidableEq, Inhabited

namespace Boolᵤ

/-- Convert to `Bool`. -/
@[coe]
public def toBool : Boolᵤ.{u} → Bool
  | .false => Bool.false
  | .true => Bool.true

/-- Convert from `Bool`. -/
public def ofBool : Bool → Boolᵤ.{u}
  | Bool.false => .false
  | Bool.true => .true

public instance : Coe Boolᵤ.{u} Bool := ⟨toBool⟩

public instance : Repr Boolᵤ.{u} := ⟨fun b => reprPrec b.toBool⟩

public instance : ToString Boolᵤ.{u} := ⟨fun b => toString b.toBool⟩

end Boolᵤ

/-- `Nat` in any universe. -/
public structure Natᵤ : Type u where
  /-- The underlying natural number. -/
  val : Nat
deriving DecidableEq, Inhabited

namespace Natᵤ

public instance : Coe Natᵤ.{u} Nat := ⟨val⟩

attribute [coe] val

public instance (n : Nat) : OfNat Natᵤ.{u} n := ⟨⟨n⟩⟩

public instance : Repr Natᵤ.{u} := ⟨fun n => reprPrec n.val⟩

public instance : ToString Natᵤ.{u} := ⟨fun n => toString n.val⟩

end Natᵤ

end ParseIt
