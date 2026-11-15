/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ParseIt

/-! Micro-benchmarks of single combinators, each with trivial, basic and simple errors. -/

open ParseIt ParseIt.Char

abbrev T := Error.Trivial
abbrev B := Error.Basic CharIterator
abbrev S := Error.Simple CharIterator

/-- Whether `p` parses `s`. -/
def ok {ε α} (p : Parser ε CharIterator Char α) (s : String) : Bool :=
  match p.parseString s with
  | .ok _ => true
  | .error _ => false

/-- Time `k` runs of `f s`, returning the median in microseconds and small allocations per run. -/
def timeRuns (k : Nat) (f : String → Bool) (s : String) : IO (Nat × Nat) := do
  let mut times := #[]
  let h₀ ← IO.getNumHeartbeats
  for _ in [0:k] do
    let t₀ ← IO.monoNanosNow
    let r := f s
    let t₁ ← IO.monoNanosNow
    unless r do throw <| IO.userError "parse failed"
    times := times.push ((t₁ - t₀) / 1000)
  let h₁ ← IO.getNumHeartbeats
  return ((times.qsort (· < ·))[k / 2]!, (h₁ - h₀) / k)

/-- Run one case with each error class in `errs`, printing a CSV line for each. -/
def run (k : Nat) (errs : List String) (name : String) (s : String)
    (pt : Parser T CharIterator Char Unit) (pb : Parser B CharIterator Char Unit)
    (ps : Parser S CharIterator Char Unit) : IO Unit := do
  for (e, f) in [("trivial", ok pt), ("basic", ok pb), ("simple", ok ps)] do
    unless errs.contains e do continue
    discard <| timeRuns 1 f s
    let (t, a) ← timeRuns k f s
    IO.println s!"{name},{e},{t},{a}"

section Parsers
variable {ε : Type} [Error ε CharIterator Char]

def dropA : Parser ε CharIterator Char Unit := dropMany (char 'a') *> endOfInput *> pure ()

def takeAny : Parser ε CharIterator Char Unit := takeMany anyToken *> endOfInput *> pure ()

def nats : Parser ε CharIterator Char Unit :=
  sepBy (char ',') ASCII.parseNat *> endOfInput *> pure ()

def ints : Parser ε CharIterator Char Unit :=
  sepBy (char ',') ASCII.parseInt *> endOfInput *> pure ()

def floats : Parser ε CharIterator Char Unit :=
  sepBy (char ',') ASCII.parseFloat *> endOfInput *> pure ()

def keywords : Parser ε CharIterator Char Unit :=
  dropMany (first [string "if", string "then", string "else", string "while", string "function"]
    *> char ' ') *> endOfInput *> pure ()

def functions : Parser ε CharIterator Char Unit :=
  dropMany (string "function") *> endOfInput *> pure ()

def comment : Parser ε CharIterator Char Unit :=
  dropUntil (string "*/") anyToken *> endOfInput *> pure ()

end Parsers

def rep (n : Nat) (s : String) : String := String.join (List.replicate n s)

/-- `micro [runs] [errors]`, where `errors` is a comma-separated list of error classes. -/
def main (args : List String) : IO Unit := do
  let k := (args.head? >>= String.toNat?).getD 11
  let errs := (args[1]?.getD "trivial,basic,simple").splitOn ","
  IO.println "case,errors,median_us,allocs"
  let s := rep 1000000 "a"
  run k errs "dropMany char, 1M" s dropA dropA dropA
  run k errs "takeMany anyToken, 1M" s takeAny takeAny takeAny
  let s := ",".intercalate ((List.range 200000).map fun i => toString (100000 + i))
  run k errs "sepBy parseNat, 200k" s nats nats nats
  let s := ",".intercalate ((List.range 200000).map fun i => if i % 2 == 0 then "7" else "-3")
  run k errs "sepBy parseInt, 200k" s ints ints ints
  let s := ",".intercalate ((List.range 100000).map fun i => s!"-{i}.25e+2")
  run k errs "sepBy parseFloat, 100k" s floats floats floats
  let kws := #["if ", "then ", "else ", "while ", "function "]
  let s := String.join ((List.range 200000).map fun i => kws[i % 5]!)
  run k errs "first of 5 keywords, 200k" s keywords keywords keywords
  let s := rep 100000 "function"
  run k errs "string \"function\", 100k" s functions functions functions
  let s := rep 1000000 "x" ++ "*/"
  run k errs "dropUntil */, 1MB" s comment comment comment
