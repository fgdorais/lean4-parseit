/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ParseIt.Basic

universe u v

namespace ParseIt
open Std

variable {ε ι τ α β γ : Type u} {m : Type u → Type v} [Iterator ι Id τ]

/-! # Token functions -/

/--
Step `it` past any `skip` steps. Calls `yield` with the next token and the iterator after it, or
`done` at the end of the input. Written in continuation-passing style so that specialization
avoids allocating an intermediate result.
-/
@[specialize]
private def nextToken [Iterators.Productive ι Id] {β : Sort _} (it : Iter (α := ι) τ)
    (yield : (rest : Iter (α := ι) τ) → Advanced rest it → τ → β) (done : Unit → β) : β :=
  match it.step with
  | ⟨.yield it' x, h⟩ => yield it' (.of_yield h) x
  | ⟨.skip it', h⟩ => nextToken it' (fun rest h' x => yield rest (h'.trans (.of_skip h)) x) done
  | ⟨.done, _⟩ => done ()
termination_by it.finitelyManySkips

/--
`tokenMap f` accepts token `t` with result `x` if `f t = some x`, otherwise fails reporting the
unexpected token.
-/
@[inline]
public def tokenMap [Iterators.Productive ι Id] [Pure m] [Error ε ι τ] (f : τ → Option α) :
    ParserT ε ι τ m α := fun it =>
  pure <| nextToken it
    (fun rest h t =>
      match f t with
      | some x => .ok rest (.moved h) x
      | none => .error (Error.unexpected it (some t)))
    (fun _ => .error (Error.unexpected it none))

/-- `anyToken` consumes and returns one token. Only fails at the end of the input. -/
@[inline]
public def anyToken [Iterators.Productive ι Id] [Pure m] [Error ε ι τ] : ParserT ε ι τ m τ :=
  tokenMap some

/-- `tokenFilter test` accepts and returns token `t` if `test t = true`. -/
@[inline]
public def tokenFilter [Iterators.Productive ι Id] [Pure m] [Error ε ι τ] (test : τ → Bool) :
    ParserT ε ι τ m τ :=
  tokenMap fun t => if test t then some t else none

/-- `token tk` accepts and returns `tk`. -/
@[inline]
public def token [Iterators.Productive ι Id] [Pure m] [Error ε ι τ] [BEq τ] (tk : τ) :
    ParserT ε ι τ m τ :=
  tokenFilter (· == tk)

/--
`tokenArray tks` accepts the tokens of `tks` in order and returns the tokens read. Fails, reporting
the first unexpected token, if any token does not match.
-/
public def tokenArray [Iterators.Productive ι Id] [Monad m] [Error ε ι τ] [BEq τ]
    (tks : Array τ) : ParserT ε ι τ m (Array τ) := do
  let mut acc := Array.emptyWithCapacity tks.size
  for tk in tks do
    acc := acc.push (← token tk)
  return acc

/--
`tokenList tks` accepts the tokens of `tks` in order and returns the tokens read. Fails, reporting
the first unexpected token, if any token does not match.
-/
public def tokenList [Iterators.Productive ι Id] [Monad m] [Error ε ι τ] [BEq τ]
    (tks : List τ) : ParserT ε ι τ m (List τ) :=
  Array.toList <$> tokenArray tks.toArray

/-- `endOfInput` succeeds only at the end of the input. Consumes no input. -/
@[inline]
public def endOfInput [Iterators.Productive ι Id] [Pure m] [Error ε ι τ] :
    ParserT ε ι τ m Unitᵤ :=
  fun it =>
    pure <| nextToken it
      (fun _ _ t => .error (Error.unexpected it (some t)))
      (fun _ => .ok it (.refl it) ⟨⟩)

/-! # Folding -/

/--
Core of the `foldl` family. Each round parses `p` and then runs the update parser `f y`. Folding
ends when a round fails, or right after a round succeeds without consuming input. The final
failed round is not consumed; its error is returned when `p` succeeded but `f` failed.
-/
@[specialize]
private def efoldlP [Iterators.Finite ι Id] [Monad m] (f : β → α → ParserT ε ι τ m β) (init : β)
    (p : ParserT ε ι τ m α) : ParserT ε ι τ m (β × Option ε) := fun it => do
  match ← p it with
  | .error _ => return .ok it (.refl it) (init, none)
  | .ok rest₁ h₁ x =>
    match ← f init x rest₁ with
    | .error e => return .ok it (.refl it) (init, some e)
    | .ok rest₂ h₂ y =>
      match h₂.trans h₁ with
      | .stay h => return .ok rest₂ (.stay h) (y, none)
      | .moved h =>
        match ← efoldlP f y p rest₂ with
        | .ok rest₃ h₃ z => return .ok rest₃ (h₃.trans (.moved h)) z
        | .error e => return .error e
termination_by it => it.finitelyManySteps
decreasing_by exact h

/--
`foldlP f init p` folds the parser function `f` from left to right using `init` as an initial value
and the parser `p` to generate inputs of type `α`. Folding ends as soon as the update parser
`p >>= f y` fails, or right after it succeeds without consuming input. This parser never fails.
-/
@[inline]
public def foldlP [Iterators.Finite ι Id] [Monad m] (f : β → α → ParserT ε ι τ m β) (init : β)
    (p : ParserT ε ι τ m α) : ParserT ε ι τ m β :=
  Prod.fst <$> efoldlP f init p

/--
`foldlM f init p` folds the monadic function `f` from left to right using `init` as an initial
value and the parser `p` to generate inputs of type `α`. Folding ends as soon as `p` fails, or
right after `p` succeeds without consuming input. This parser never fails.
-/
@[inline]
public def foldlM [Iterators.Finite ι Id] [Monad m] (f : β → α → m β) (init : β)
    (p : ParserT ε ι τ m α) : ParserT ε ι τ m β :=
  foldlP (fun y x => monadLift (f y x)) init p

/--
`foldl f init p` folds the function `f` from left to right using `init` as an initial value and the
parser `p` to generate inputs of type `α`. Folding ends as soon as `p` fails, or right after `p`
succeeds without consuming input. This parser never fails.
-/
@[inline]
public def foldl [Iterators.Finite ι Id] [Monad m] (f : β → α → β) (init : β)
    (p : ParserT ε ι τ m α) : ParserT ε ι τ m β :=
  foldlP (fun y x => pure (f y x)) init p

/--
`foldr f p q` parses `p` repeatedly until it fails and then parses `q`, folding `f` from right to
left over the results, starting from the result of `q`. Repetition also ends right after `p`
succeeds without consuming input. If `q` fails after some occurrences of `p` then the parse is
retried with fewer occurrences.
-/
@[specialize]
public def foldr [Iterators.Finite ι Id] [Monad m] (f : α → β → β) (p : ParserT ε ι τ m α)
    (q : ParserT ε ι τ m β) : ParserT ε ι τ m β := fun it => do
  match ← p it with
  | .ok rest (.moved h) x =>
    match ← foldr f p q rest with
    | .ok rest' h' y => return .ok rest' (h'.trans (.moved h)) (f x y)
    | .error _ => q it
  | .ok rest (.stay h) x =>
    match ← q rest with
    | .ok rest' h' y => return .ok rest' (h'.trans (.stay h)) (f x y)
    | .error _ => q it
  | .error _ => q it
termination_by it => it.finitelyManySteps
decreasing_by exact h

/--
`foldlN n f init p` folds the function `f` from left to right using `init` as an initial value over
the results of exactly `n` occurrences of `p`. Fails if any occurrence of `p` fails.
-/
@[specialize]
public def foldlN [Monad m] (n : Nat) (f : β → α → β) (init : β) (p : ParserT ε ι τ m α) :
    ParserT ε ι τ m β :=
  match n with
  | 0 => pure init
  | n + 1 => do foldlN n f (f init (← p)) p

/--
`foldlUpTo n f init p` folds the function `f` from left to right using `init` as an initial value
over the results of up to `n` occurrences of `p`. Folding ends early when `p` fails. This parser
never fails.
-/
@[specialize]
public def foldlUpTo [Monad m] (n : Nat) (f : β → α → β) (init : β) (p : ParserT ε ι τ m α) :
    ParserT ε ι τ m β :=
  match n with
  | 0 => pure init
  | n + 1 => do
    match ← option? p with
    | some x => foldlUpTo n f (f init x) p
    | none => pure init

/--
`foldlUntil f init stop p` folds the function `f` from left to right using `init` as an initial
value over the results of zero or more occurrences of `p` until `stop` succeeds, and returns the
result of folding with the result of `stop`. If `p` fails before `stop` succeeds then the error from
`p` is reported. If `p` succeeds without consuming input then the error from `stop` is reported.
-/
@[specialize]
public def foldlUntil [Iterators.Finite ι Id] [Monad m] (f : γ → α → γ) (init : γ)
    (stop : ParserT ε ι τ m β) (p : ParserT ε ι τ m α) : ParserT ε ι τ m (γ × β) := fun it => do
  match ← stop it with
  | .ok rest h y => return .ok rest h (init, y)
  | .error e =>
    match ← p it with
    | .error e => return .error e
    | .ok _ (.stay _) _ => return .error e
    | .ok rest (.moved h) x =>
      match ← foldlUntil f (f init x) stop p rest with
      | .ok rest' h' z => return .ok rest' (h'.trans (.moved h)) z
      | .error e => return .error e
termination_by it => it.finitelyManySteps
decreasing_by exact h

/-! # `take` family -/

/-- `take n p` parses exactly `n` occurrences of `p` and returns the array of results. -/
@[inline]
public def take [Monad m] (n : Nat) (p : ParserT ε ι τ m α) : ParserT ε ι τ m (Array α) :=
  foldlN n Array.push (.emptyWithCapacity n) p

/--
`takeUpTo n p` parses up to `n` occurrences of `p` and returns the array of results. This parser
never fails.
-/
@[inline]
public def takeUpTo [Monad m] (n : Nat) (p : ParserT ε ι τ m α) : ParserT ε ι τ m (Array α) :=
  foldlUpTo n Array.push #[] p

/--
`takeMany p` parses zero or more occurrences of `p` until it fails and returns the array of results.
This parser never fails.
-/
@[inline]
public def takeMany [Iterators.Finite ι Id] [Monad m] (p : ParserT ε ι τ m α) :
    ParserT ε ι τ m (Array α) :=
  foldl Array.push #[] p

/--
`takeMany1 p` parses one or more occurrences of `p` until it fails and returns the array of
results.
-/
@[inline]
public def takeMany1 [Iterators.Finite ι Id] [Monad m] (p : ParserT ε ι τ m α) :
    ParserT ε ι τ m (Array α) := do
  foldl Array.push #[← p] p

/--
`takeManyN n p` parses `n` or more occurrences of `p` until it fails and returns the array of
results.
-/
@[inline]
public def takeManyN [Iterators.Finite ι Id] [Monad m] (n : Nat) (p : ParserT ε ι τ m α) :
    ParserT ε ι τ m (Array α) := do
  foldl Array.push (← take n p) p

/--
`takeUntil stop p` parses zero or more occurrences of `p` until `stop` succeeds, and returns the
array of results of `p` and the result of `stop`. If `p` fails before `stop` succeeds then the error
from `p` is reported. If `p` succeeds without consuming input then the error from `stop` is
reported.
-/
@[inline]
public def takeUntil [Iterators.Finite ι Id] [Monad m] (stop : ParserT ε ι τ m β)
    (p : ParserT ε ι τ m α) : ParserT ε ι τ m (Array α × β) :=
  foldlUntil Array.push #[] stop p

/-! # `drop` family -/

/-- `drop n p` parses exactly `n` occurrences of `p`, ignoring the results. -/
@[inline]
public def drop [Monad m] (n : Nat) (p : ParserT ε ι τ m α) : ParserT ε ι τ m Unitᵤ :=
  foldlN n (fun _ _ => ⟨⟩) ⟨⟩ p

/-- `dropUpTo n p` parses up to `n` occurrences of `p`, ignoring the results. Never fails. -/
@[inline]
public def dropUpTo [Monad m] (n : Nat) (p : ParserT ε ι τ m α) : ParserT ε ι τ m Unitᵤ :=
  foldlUpTo n (fun _ _ => ⟨⟩) ⟨⟩ p

/--
`dropMany p` parses zero or more occurrences of `p` until it fails, ignoring the results. This
parser never fails.
-/
@[inline]
public def dropMany [Iterators.Finite ι Id] [Monad m] (p : ParserT ε ι τ m α) :
    ParserT ε ι τ m Unitᵤ :=
  foldl (fun _ _ => ⟨⟩) ⟨⟩ p

/-- `dropMany1 p` parses one or more occurrences of `p` until it fails, ignoring the results. -/
@[inline]
public def dropMany1 [Iterators.Finite ι Id] [Monad m] (p : ParserT ε ι τ m α) :
    ParserT ε ι τ m Unitᵤ :=
  p *> dropMany p

/-- `dropManyN n p` parses `n` or more occurrences of `p` until it fails, ignoring the results. -/
@[inline]
public def dropManyN [Iterators.Finite ι Id] [Monad m] (n : Nat) (p : ParserT ε ι τ m α) :
    ParserT ε ι τ m Unitᵤ :=
  drop n p *> dropMany p

/--
`dropUntil stop p` parses zero or more occurrences of `p` until `stop` succeeds, and returns the
result of `stop`, ignoring the results of `p`. Errors are reported as for `takeUntil`.
-/
@[inline]
public def dropUntil [Iterators.Finite ι Id] [Monad m] (stop : ParserT ε ι τ m β)
    (p : ParserT ε ι τ m α) : ParserT ε ι τ m β :=
  Prod.snd <$> foldlUntil (γ := Unitᵤ) (fun _ _ => ⟨⟩) ⟨⟩ stop p

/-! # `count` family -/

/--
`count p` parses zero or more occurrences of `p` until it fails and returns the number of
successes. This parser never fails.
-/
@[inline]
public def count [Iterators.Finite ι Id] [Monad m] (p : ParserT ε ι τ m α) :
    ParserT ε ι τ m Natᵤ :=
  foldl (fun n _ => ⟨n.val + 1⟩) 0 p

/--
`countUpTo n p` parses up to `n` occurrences of `p` and returns the number of successes. This
parser never fails.
-/
@[inline]
public def countUpTo [Monad m] (n : Nat) (p : ParserT ε ι τ m α) : ParserT ε ι τ m Natᵤ :=
  foldlUpTo n (fun n _ => ⟨n.val + 1⟩) 0 p

/--
`countUntil stop p` parses zero or more occurrences of `p` until `stop` succeeds, and returns the
number of occurrences of `p` and the result of `stop`. Errors are reported as for `takeUntil`.
-/
@[inline]
public def countUntil [Iterators.Finite ι Id] [Monad m] (stop : ParserT ε ι τ m β)
    (p : ParserT ε ι τ m α) : ParserT ε ι τ m (Natᵤ × β) :=
  foldlUntil (fun n _ => ⟨n.val + 1⟩) 0 stop p

/-! # `endBy` family -/

@[inline]
private def endByCore [Iterators.Finite ι Id] [Monad m] (sep : ParserT ε ι τ m β)
    (p : ParserT ε ι τ m α) (init : Array α) (strict : Bool) : ParserT ε ι τ m (Array α) := do
  match ← efoldlP (fun xs x => sep *> pure (xs.push x)) init p with
  | (xs, some e) => if strict then throw e else pure xs
  | (xs, none) => pure xs

/--
`endBy sep p` parses zero or more occurrences of `p`, each followed by `sep`, and returns the array
of results of `p`.

The optional `strict` parameter controls error reporting:

* If `strict = false` then this parser never fails and returns the longest possible array.
* If `strict = true` then this parser fails if there is a final occurrence of `p` without a
  trailing `sep`. Then the error of `sep` is reported.
-/
@[inline]
public def endBy [Iterators.Finite ι Id] [Monad m] (sep : ParserT ε ι τ m β)
    (p : ParserT ε ι τ m α) (strict : Bool := false) : ParserT ε ι τ m (Array α) :=
  endByCore sep p #[] strict

/--
`endBy1 sep p` parses one or more occurrences of `p`, each followed by `sep`, and returns the array
of results of `p`. The optional `strict` parameter controls error reporting after the first
occurrence, as for `endBy`.
-/
@[inline]
public def endBy1 [Iterators.Finite ι Id] [Monad m] (sep : ParserT ε ι τ m β)
    (p : ParserT ε ι τ m α) (strict : Bool := false) : ParserT ε ι τ m (Array α) := do
  endByCore sep p #[← p <* sep] strict

/-! # `sepBy` family -/

@[inline]
private def sepByCore [Iterators.Finite ι Id] [Monad m] (sep : ParserT ε ι τ m β)
    (p : ParserT ε ι τ m α) (init : Array α) (strict : Bool) : ParserT ε ι τ m (Array α) := do
  match ← efoldlP (fun xs _ => (xs.push ·) <$> p) init sep with
  | (xs, some e) => if strict then throw e else pure xs
  | (xs, none) => pure xs

/--
`sepBy sep p` parses zero or more occurrences of `p` separated by `sep`, and returns the array of
results of `p`.

The optional `strict` parameter controls error reporting:

* If `strict = false` then this parser never fails and returns the longest possible array.
* If `strict = true` then this parser fails if there is a final `sep` without a following `p`.
  Then the error of `p` is reported.
-/
@[inline]
public def sepBy [Iterators.Finite ι Id] [Monad m] (sep : ParserT ε ι τ m β)
    (p : ParserT ε ι τ m α) (strict : Bool := false) : ParserT ε ι τ m (Array α) := do
  match ← option? p with
  | some x => sepByCore sep p #[x] strict
  | none => pure #[]

/--
`sepBy1 sep p` parses one or more occurrences of `p` separated by `sep`, and returns the array of
results of `p`. The optional `strict` parameter controls error reporting after the first
occurrence, as for `sepBy`.
-/
@[inline]
public def sepBy1 [Iterators.Finite ι Id] [Monad m] (sep : ParserT ε ι τ m β)
    (p : ParserT ε ι τ m α) (strict : Bool := false) : ParserT ε ι τ m (Array α) := do
  sepByCore sep p #[← p] strict

/--
`sepNoEndBy sep p` parses zero or more occurrences of `p` separated by `sep` without a trailing
`sep`, and returns the array of results of `p`.
-/
@[inline]
public def sepNoEndBy [Iterators.Finite ι Id] [Monad m] (sep : ParserT ε ι τ m β)
    (p : ParserT ε ι τ m α) : ParserT ε ι τ m (Array α) :=
  sepBy sep p true

/--
`sepNoEndBy1 sep p` parses one or more occurrences of `p` separated by `sep` without a trailing
`sep`, and returns the array of results of `p`.
-/
@[inline]
public def sepNoEndBy1 [Iterators.Finite ι Id] [Monad m] (sep : ParserT ε ι τ m β)
    (p : ParserT ε ι τ m α) : ParserT ε ι τ m (Array α) :=
  sepBy1 sep p true

/--
`sepEndBy sep p` parses zero or more occurrences of `p` separated by `sep` with an optional
trailing `sep`, and returns the array of results of `p`. This parser never fails.
-/
@[inline]
public def sepEndBy [Iterators.Finite ι Id] [Monad m] (sep : ParserT ε ι τ m β)
    (p : ParserT ε ι τ m α) : ParserT ε ι τ m (Array α) :=
  sepBy sep p <* optional sep

/--
`sepEndBy1 sep p` parses one or more occurrences of `p` separated by `sep` with an optional
trailing `sep`, and returns the array of results of `p`.
-/
@[inline]
public def sepEndBy1 [Iterators.Finite ι Id] [Monad m] (sep : ParserT ε ι τ m β)
    (p : ParserT ε ι τ m α) : ParserT ε ι τ m (Array α) :=
  sepBy1 sep p <* optional sep

end ParseIt
