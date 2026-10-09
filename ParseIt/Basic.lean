/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ParseIt.Error
public import ParseIt.Prelude

/-! # ParseIt core

Parsers read tokens from a pure iterator `Std.Iter (α := ι) τ`. The parser state is the iterator
itself, so backtracking is simply reusing an earlier iterator value.

Every successful parse reports its `Progress`: either the iterator did not move, or it moved
strictly forward along plausible successor steps. Proofs are erased at runtime, so `Progress`
compiles to a one-bit tag, and that tag is what allows repetition combinators to be total.
-/

universe u v

namespace ParseIt
open Std

variable {ε ι τ α β : Type u} {m : Type u → Type v} [Iterator ι Id τ]

/-- `it'` is reachable from `it` by one or more plausible successor steps. -/
@[expose]
public def Advanced (it' it : Iter (α := ι) τ) : Prop :=
  IterM.TerminationMeasures.Finite.Rel it'.finitelyManySteps! it.finitelyManySteps!

public theorem Advanced.trans {it'' it' it : Iter (α := ι) τ} :
    Advanced it'' it' → Advanced it' it → Advanced it'' it :=
  Relation.TransGen.trans

public theorem Advanced.of_yield {it' it : Iter (α := ι) τ} {out : τ}
    (h : it.IsPlausibleStep (.yield it' out)) : Advanced it' it :=
  IterM.TerminationMeasures.Finite.rel_of_yield h

public theorem Advanced.of_skip {it' it : Iter (α := ι) τ}
    (h : it.IsPlausibleStep (.skip it')) : Advanced it' it :=
  IterM.TerminationMeasures.Finite.rel_of_skip h

/-- How far a parser moved the iterator from `it` to `it'`. -/
public inductive Progress (it' it : Iter (α := ι) τ) : Type u where
  /-- The iterator did not move. -/
  | stay : it' = it → Progress it' it
  /-- The iterator moved strictly forward. -/
  | moved : Advanced it' it → Progress it' it

namespace Progress

/-- Whether the iterator moved. -/
@[inline]
public def isMoved {it' it : Iter (α := ι) τ} : Progress it' it → Bool
  | .stay _ => false
  | .moved _ => true

/-- No progress. -/
@[inline]
public def refl (it : Iter (α := ι) τ) : Progress it it := .stay rfl

/-- Compose progress. -/
@[inline]
public def trans {it'' it' it : Iter (α := ι) τ} :
    Progress it'' it' → Progress it' it → Progress it'' it
  | .stay h₁, .stay h₂ => .stay (h₁.trans h₂)
  | .stay h₁, .moved h₂ => .moved (h₁ ▸ h₂)
  | .moved h₁, .stay h₂ => .moved (h₂ ▸ h₁)
  | .moved h₁, .moved h₂ => .moved (h₁.trans h₂)

/-- Strict progress followed by any progress is strict progress. -/
private theorem advanced_of_trans {it'' it' it : Iter (α := ι) τ} :
    Progress it'' it' → Advanced it' it → Advanced it'' it
  | .stay h₁, h₂ => h₁ ▸ h₂
  | .moved h₁, h₂ => h₁.trans h₂

end Progress

/-- Parser result for a parse starting at iterator `it`. -/
public inductive Result (ε : Type u) (it : Iter (α := ι) τ) (α : Type u) : Type u where
  /-- Success, with the remaining iterator and the progress made. -/
  | ok (rest : Iter (α := ι) τ) (progress : Progress rest it) (value : α)
  /-- Failure. No input is consumed on failure. -/
  | error (err : ε)

/--
`ParserT ε ι τ m` is a monad transformer to parse tokens of type `τ` from an iterator with internal
state `ι`, with error type `ε`.
-/
@[expose]
public def ParserT (ε ι τ : Type u) [Iterator ι Id τ] (m : Type u → Type v) (α : Type u) :
    Type (max u v) :=
  (it : Iter (α := ι) τ) → m (Result ε it α)

/-- `Parser ε ι τ` is the parser monad without an underlying monad. -/
public abbrev Parser (ε ι τ : Type u) [Iterator ι Id τ] := ParserT ε ι τ Id

namespace ParserT

/-- Run parser `p` on iterator `it`. -/
@[inline]
public def run (p : ParserT ε ι τ m α) (it : Iter (α := ι) τ) : m (Result ε it α) := p it

public instance [Monad m] : Monad (ParserT ε ι τ m) where
  pure x it := pure (.ok it (.refl it) x)
  bind p f it := do
    match ← p it with
    | .ok rest h₁ x =>
      match ← f x rest with
      | .ok rest' h₂ y => return .ok rest' (h₂.trans h₁) y
      | .error e => return .error e
    | .error e => return .error e

public instance [Monad m] : MonadExceptOf ε (ParserT ε ι τ m) where
  throw e _ := return .error e
  tryCatch p c it := do
    match ← p it with
    | .ok rest h x => return .ok rest h x
    | .error e => c e it

public instance [Monad m] : MonadLift m (ParserT ε ι τ m) where
  monadLift x it := return .ok it (.refl it) (← x)

/-- `p <|> q` runs `q` from the same starting point when `p` fails, merging both errors. -/
public instance [Monad m] [Error ε ι τ] : OrElse (ParserT ε ι τ m α) where
  orElse p q it := do
    match ← p it with
    | .ok rest h x => return .ok rest h x
    | .error e₁ =>
      match ← q () it with
      | .ok rest h x => return .ok rest h x
      | .error e₂ => return .error (Error.merge (ι := ι) e₁ e₂)

end ParserT

/-- Run parser `p` on iterator `it`. -/
@[inline]
public protected def Parser.run (p : Parser ε ι τ α) (it : Iter (α := ι) τ) : Result ε it α :=
  p it

/-- Run parser `p` on iterator `it`, returning the parsed value or the error. -/
@[inline]
public def Parser.parse (p : Parser ε ι τ α) (it : Iter (α := ι) τ) : Except ε α :=
  match p.run it with
  | .ok _ _ x => .ok x
  | .error e => .error e

/-! # Positions and errors -/

/-- Get the current iterator. -/
@[inline]
private def getIter [Pure m] : ParserT ε ι τ m (Iter (α := ι) τ) :=
  fun it => pure (.ok it (.refl it) it)

/-- `getPos` returns the current input position. Consumes no input and never fails. -/
@[inline]
public def getPos [Pure m] [HasPos ι τ] : ParserT ε ι τ m (HasPos.Pos ι) :=
  fun it => pure (.ok it (.refl it) (HasPos.pos it))

/--
`withSpan p` parses `p` and returns its result together with the input positions where `p` started
and stopped.
-/
@[inline]
public def withSpan [Monad m] [HasPos ι τ] (p : ParserT ε ι τ m α) :
    ParserT ε ι τ m (α × HasPos.Pos ι × HasPos.Pos ι) := fun it => do
  match ← p it with
  | .ok rest h x => return .ok rest h (x, HasPos.pos it, HasPos.pos rest)
  | .error e => return .error e

/-- Throw an unexpected input error at the current position. -/
@[inline]
public def throwUnexpected [Pure m] [Error ε ι τ] (input : Option τ := none) :
    ParserT ε ι τ m α :=
  fun it => pure (.error (Error.unexpected it input))

/-- Throw an unexpected input error with an additional message. -/
@[inline]
public def throwUnexpectedWithMessage [Pure m] [Error ε ι τ] (input : Option τ := none)
    (msg : String) : ParserT ε ι τ m α :=
  fun it => pure (.error (Error.addMessage (Error.unexpected it input) it msg))

/-- Add a message to errors reported by `p`. -/
@[inline]
public def withErrorMessage [Monad m] [Error ε ι τ] (msg : String) (p : ParserT ε ι τ m α) :
    ParserT ε ι τ m α := fun it => do
  match ← p it with
  | .ok rest h x => return .ok rest h x
  | .error e => return .error (Error.addMessage e it msg)

/-! # Basic combinators -/

/--
`lookAhead p` parses `p` without consuming any input. If `p` fails then `lookAhead p` fails with the
same error.
-/
@[inline]
public def lookAhead [Monad m] (p : ParserT ε ι τ m α) : ParserT ε ι τ m α := fun it => do
  match ← p it with
  | .ok _ _ x => return .ok it (.refl it) x
  | .error e => return .error e

/-- `notFollowedBy p` succeeds only if `p` fails. Consumes no input. -/
@[inline]
public def notFollowedBy [Monad m] [Error ε ι τ] (p : ParserT ε ι τ m α) :
    ParserT ε ι τ m Unitᵤ :=
  fun it => do
    match ← p it with
    | .ok _ _ _ => return .error (Error.unexpected it none)
    | .error _ => return .ok it (.refl it) ⟨⟩

/-! ### `option` family -/

/--
`eoption p` tries to parse `p` and returns `Sum.inl x` if `p` returns `x`, or `Sum.inr e` if `p`
fails with error `e`. This parser never fails.
-/
@[inline]
private def eoption [Monad m] (p : ParserT ε ι τ m α) : ParserT ε ι τ m (Sum α ε) := fun it => do
  match ← p it with
  | .ok rest h x => return .ok rest h (.inl x)
  | .error e => return .ok it (.refl it) (.inr e)

/--
`optionD p default` tries to parse `p` and returns `x` if `p` returns `x`, otherwise returns the
monadic value `default`. This parser never fails.
-/
@[inline]
public def optionD [Monad m] (p : ParserT ε ι τ m α) (default : m α) : ParserT ε ι τ m α := do
  match ← eoption p with
  | .inl x => return x
  | .inr _ => default

/--
`option! p` tries to parse `p` and returns `x` if `p` returns `x`, otherwise returns
`Inhabited.default`. This parser never fails.
-/
@[inline]
public def option! [Monad m] [Inhabited α] (p : ParserT ε ι τ m α) : ParserT ε ι τ m α :=
  optionD p (pure default)

/--
`option? p` tries to parse `p` and returns `some x` if `p` returns `x`, otherwise returns `none`.
This parser never fails.
-/
@[inline]
public def option? [Monad m] (p : ParserT ε ι τ m α) : ParserT ε ι τ m (Option α) :=
  optionD (some <$> p) (pure none)

/-- `optional p` tries to parse `p`, ignoring its output and errors. This parser never fails. -/
@[inline]
public def optional [Monad m] (p : ParserT ε ι τ m α) : ParserT ε ι τ m Unitᵤ :=
  optionD (p *> pure ⟨⟩) (pure ⟨⟩)

/--
`test p` returns `true` if `p` succeeds and `false` otherwise. This parser never fails.
-/
@[inline]
public def test [Monad m] (p : ParserT ε ι τ m α) : ParserT ε ι τ m Boolᵤ :=
  optionD (p *> pure .true) (pure .false)

/-! ### `first` family -/

/--
`first ps` tries the parsers from the list `ps` in order until one succeeds and returns its result.

When all parsers fail, their errors are folded with `combine`, starting from an unexpected input
error at the current position. The default is `Error.merge`.
-/
public def first [Monad m] [Error ε ι τ] (ps : List (ParserT ε ι τ m α))
    (combine : ε → ε → ε := Error.merge (ι := ι)) : ParserT ε ι τ m α :=
  fun it => loop ps (Error.unexpected it none) it
where
  loop : List (ParserT ε ι τ m α) → ε → ParserT ε ι τ m α
  | [], e, _ => pure (.error e)
  | p :: ps, e, it => do
    match ← p it with
    | .ok rest h x => pure (.ok rest h x)
    | .error f => loop ps (combine e f) it

end ParseIt
