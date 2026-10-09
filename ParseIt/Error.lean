/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ParseIt.Prelude

/-! # Parser errors

The class `ParseIt.Error` is used throughout the library to report parsing errors. Users are
encouraged to provide instances tailored to their applications.

Three general purpose instances are provided:

* `Error.Trivial` discards all error information.
* `Error.Basic` records the position and offending token of the furthest error.
* `Error.Simple` records all error information, without processing.
-/

universe u v

namespace ParseIt
open Std

variable {ι τ : Type u} [Iterator ι Id τ]

/-- Position information for error reporting. -/
public class HasPos (ι : Type u) (τ : outParam (Type u)) [Iterator ι Id τ] where
  /-- Position type. -/
  Pos : Type u
  /-- Current position of an iterator. -/
  pos : Iter (α := ι) τ → Pos
attribute [reducible] HasPos.Pos

/-- *Parser error class*

* `unexpected it t` reports unexpected input at iterator `it`, optionally with the offending token.
* `addMessage e it msg` adds information to error `e` at iterator `it`.
* `merge e₁ e₂` combines the errors of two failed alternatives; by default it keeps `e₂`.
-/
public class Error (ε : Type u) (ι : Type u) (τ : outParam (Type u)) [Iterator ι Id τ] where
  unexpected : Iter (α := ι) τ → Option τ → ε
  addMessage : ε → Iter (α := ι) τ → String → ε
  merge : ε → ε → ε := fun _ e => e

namespace Error

/-- *Trivial error type*: discards all error information. -/
public abbrev Trivial : Type u := Unitᵤ

public instance : Error Trivial ι τ where
  unexpected _ _ := ⟨⟩
  addMessage _ _ _ := ⟨⟩

/--
*Basic error type*: the position and, optionally, the offending token. Merging keeps the error at
the furthest position, preferring the later alternative on ties. Messages are discarded.
-/
public structure Basic (ι : Type u) {τ : Type u} [Iterator ι Id τ] [HasPos ι τ] where
  /-- Position of the error. -/
  pos : HasPos.Pos ι
  /-- Offending token, if any. -/
  token : Option τ

public instance [HasPos ι τ] [LE (HasPos.Pos ι)] [DecidableLE (HasPos.Pos ι)] :
    Error (Basic ι) ι τ where
  unexpected it t := ⟨HasPos.pos it, t⟩
  addMessage e _ _ := e
  merge e₁ e₂ := if e₁.pos ≤ e₂.pos then e₂ else e₁

public instance [HasPos ι τ] [Repr τ] [Repr (HasPos.Pos ι)] : ToString (Basic ι) where
  toString
    | ⟨pos, some t⟩ => s!"unexpected input {repr t} at {repr pos}"
    | ⟨pos, none⟩ => s!"unexpected input at {repr pos}"

/-- *Simple error type*: records all error information, without processing. -/
public inductive Simple (ι : Type u) {τ : Type u} [Iterator ι Id τ] [HasPos ι τ] where
  /-- Unexpected input at a position. -/
  | unexpected : HasPos.Pos ι → Option τ → Simple ι
  /-- Error with an additional message at a position. -/
  | addMessage : Simple ι → HasPos.Pos ι → String → Simple ι
  /-- Errors from two failed alternatives. -/
  | merge : Simple ι → Simple ι → Simple ι

public instance [HasPos ι τ] : Error (Simple ι) ι τ where
  unexpected it t := .unexpected (HasPos.pos it) t
  addMessage e it msg := .addMessage e (HasPos.pos it) msg
  merge := .merge

/-- Render a simple error, listing alternatives separated by `" or "`. -/
public protected def Simple.toString [HasPos ι τ] [Repr τ] [Repr (HasPos.Pos ι)] :
    Simple ι → String
  | .unexpected pos (some t) => s!"unexpected input {repr t} at {repr pos}"
  | .unexpected pos none => s!"unexpected input at {repr pos}"
  | .addMessage e pos msg => Simple.toString e ++ s!"; {msg} at {repr pos}"
  | .merge e₁ e₂ => Simple.toString e₁ ++ " or " ++ Simple.toString e₂

public instance [HasPos ι τ] [Repr τ] [Repr (HasPos.Pos ι)] : ToString (Simple ι) where
  toString := Simple.toString

end Error

end ParseIt
