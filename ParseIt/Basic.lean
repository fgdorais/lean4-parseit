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

/--
Hint after a success with hint `h₁` followed by a parse with progress `p` and hint `h₂`. The hints
`h₁` are only relevant where the first parse stopped, so they are dropped when the second parse
moved.
-/
@[inline]
public def mergeHints [Error ε ι τ] {it' it : Iter (α := ι) τ} (p : Progress it' it)
    (h₁ h₂ : Option ε) : Option ε :=
  if p.isMoved then h₂ else Error.mergeHints (ι := ι) h₁ h₂

end Progress

/--
Parser result for a parse starting at iterator `it`.

A success can carry a *hint*: the error of an alternative that was given up on where the parse
stopped, such as the failed last round of a repetition. When the next parser fails without moving,
the hint is merged into its error, so that errors further along are not lost.
-/
public inductive Result (ε : Type u) (it : Iter (α := ι) τ) (α : Type u) : Type u where
  /-- Success, with the remaining iterator, the progress made, and an optional hint. -/
  | ok (rest : Iter (α := ι) τ) (progress : Progress rest it) (value : α) (hint : Option ε)
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

/--
Hints of `p` are merged into the errors of `f`, and are kept with the hints of `f` when `f`
succeeds without moving.
-/
public instance [Monad m] [Error ε ι τ] : Monad (ParserT ε ι τ m) where
  pure x it := pure (.ok it (.refl it) x none)
  bind p f it := do
    match ← p it with
    | .ok rest h₁ x hint₁ =>
      match ← f x rest with
      | .ok rest' h₂ y hint₂ => return .ok rest' (h₂.trans h₁) y (h₂.mergeHints hint₁ hint₂)
      | .error e => return .error (Error.mergeHint (ι := ι) hint₁ e)
    | .error e => return .error e

public instance [Monad m] : MonadExceptOf ε (ParserT ε ι τ m) where
  throw e _ := return .error e
  tryCatch p c it := do
    match ← p it with
    | .ok rest h x hint => return .ok rest h x hint
    | .error e => c e it

public instance [Monad m] : MonadLift m (ParserT ε ι τ m) where
  monadLift x it := return .ok it (.refl it) (← x) none

/--
`p <|> q` runs `q` from the same starting point when `p` fails, merging both errors. When `q`
succeeds without moving, the error of `p` is kept as a hint.
-/
public instance [Monad m] [Error ε ι τ] : OrElse (ParserT ε ι τ m α) where
  orElse p q it := do
    match ← p it with
    | .ok rest h x hint => return .ok rest h x hint
    | .error e₁ =>
      match ← q () it with
      | .ok rest h x hint => return .ok rest h x (h.mergeHints (some e₁) hint)
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
  | .ok _ _ x _ => .ok x
  | .error e => .error e

/-! # Positions and errors -/

/-- Get the current iterator. -/
@[inline]
private def getIter [Pure m] : ParserT ε ι τ m (Iter (α := ι) τ) :=
  fun it => pure (.ok it (.refl it) it none)

/-- `getPos` returns the current input position. Consumes no input and never fails. -/
@[inline]
public def getPos [Pure m] [HasPos ι τ] : ParserT ε ι τ m (HasPos.Pos ι) :=
  fun it => pure (.ok it (.refl it) (HasPos.pos it) none)

/--
`withSpan p` parses `p` and returns its result together with the input positions where `p` started
and stopped.
-/
@[inline]
public def withSpan [Monad m] [HasPos ι τ] (p : ParserT ε ι τ m α) :
    ParserT ε ι τ m (α × HasPos.Pos ι × HasPos.Pos ι) := fun it => do
  match ← p it with
  | .ok rest h x hint => return .ok rest h (x, HasPos.pos it, HasPos.pos rest) hint
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
  | .ok rest h x hint => return .ok rest h x hint
  | .error e => return .error (Error.addMessage e it msg)

/-! # Basic combinators -/

/--
`lookAhead p` parses `p` without consuming any input. If `p` fails then `lookAhead p` fails with the
same error. The hints of `p` are kept only when `p` did not move.
-/
@[inline]
public def lookAhead [Monad m] (p : ParserT ε ι τ m α) : ParserT ε ι τ m α := fun it => do
  match ← p it with
  | .ok _ h x hint => return .ok it (.refl it) x (if h.isMoved then none else hint)
  | .error e => return .error e

/-- `notFollowedBy p` succeeds only if `p` fails. Consumes no input. -/
@[inline]
public def notFollowedBy [Monad m] [Error ε ι τ] (p : ParserT ε ι τ m α) :
    ParserT ε ι τ m Unitᵤ :=
  fun it => do
    match ← p it with
    | .ok _ _ _ _ => return .error (Error.unexpected it none)
    | .error _ => return .ok it (.refl it) ⟨⟩ none

/-! ### `option` family -/

/--
`optionD p default` tries to parse `p` and returns `x` if `p` returns `x`, otherwise returns the
monadic value `default`, keeping the error of `p` as a hint. This parser never fails.
-/
@[inline]
public def optionD [Monad m] (p : ParserT ε ι τ m α) (default : m α) : ParserT ε ι τ m α :=
  fun it => do
    match ← p it with
    | .ok rest h x hint => return .ok rest h x hint
    | .error e => return .ok it (.refl it) (← default) (some e)

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
public def option? [Monad m] [Error ε ι τ] (p : ParserT ε ι τ m α) : ParserT ε ι τ m (Option α) :=
  optionD (some <$> p) (pure none)

/-- `optional p` tries to parse `p`, ignoring its output and errors. This parser never fails. -/
@[inline]
public def optional [Monad m] [Error ε ι τ] (p : ParserT ε ι τ m α) : ParserT ε ι τ m Unitᵤ :=
  optionD (p *> pure ⟨⟩) (pure ⟨⟩)

/--
`test p` returns `true` if `p` succeeds and `false` otherwise. This parser never fails.
-/
@[inline]
public def test [Monad m] [Error ε ι τ] (p : ParserT ε ι τ m α) : ParserT ε ι τ m Boolᵤ :=
  optionD (p *> pure .true) (pure .false)

/-! ### `first` family -/

/--
`first ps` tries the parsers from the list `ps` in order until one succeeds and returns its result.

When all parsers fail, their errors are folded with `combine`, from left to right. The default is
`Error.merge`. When `ps` is empty, an unexpected input error at the current position is reported.
-/
public def first [Monad m] [Error ε ι τ] (ps : List (ParserT ε ι τ m α))
    (combine : ε → ε → ε := Error.merge (ι := ι)) : ParserT ε ι τ m α :=
  fun it => match ps with
    | [] => pure (.error (Error.unexpected it none))
    | p :: ps => do
      match ← p it with
      | .ok rest h x hint => pure (.ok rest h x hint)
      | .error e => loop ps e it
where
  /--
  Try the parsers `ps` after earlier alternatives failed with error `e`, which is kept as a hint
  when an alternative succeeds without moving.
  -/
  loop : List (ParserT ε ι τ m α) → ε → ParserT ε ι τ m α
  | [], e, _ => pure (.error e)
  | p :: ps, e, it => do
    match ← p it with
    | .ok rest h x hint => pure (.ok rest h x (h.mergeHints (some e) hint))
    | .error f => loop ps (combine e f) it

end ParseIt
