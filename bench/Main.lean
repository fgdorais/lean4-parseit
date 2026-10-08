import Bench.ParseItJSON
import Bench.ParserJSON
import Bench.ParseItJSONTrivial
import Bench.ParserJSONTrivial

/-- A JSON document with `n` records, exercising strings, escapes, numbers and nesting. -/
def genJSON (n : Nat) : String := Id.run do
  let mut s := "[\n"
  for i in [0:n] do
    if i > 0 then s := s ++ ",\n"
    s := s ++ s!"  \{\"id\": {i}, \"name\": \"item {i} \\\"quoted\\\" \\u00e9\", " ++
      s!"\"score\": -{i}.25e+2, \"ok\": true, \"tags\": [\"a\", \"b\", \"c\"], " ++
      "\"nested\": {\"x\": null, \"y\": [1, 2, [3, 4]]}}"
  s ++ "\n]\n"

/-- Time `k` runs of `f s`, returning the median in microseconds and small allocations per run. -/
def timeRuns (k : Nat) (f : String → Bool) (s : String) : IO (Nat × Nat) := do
  let mut times := #[]
  let h₀ ← IO.getNumHeartbeats
  for _ in [0:k] do
    let t₀ ← IO.monoNanosNow
    let ok := f s
    let t₁ ← IO.monoNanosNow
    unless ok do throw <| IO.userError "validation failed"
    times := times.push ((t₁ - t₀) / 1000)
  let h₁ ← IO.getNumHeartbeats
  let sorted := times.qsort (· < ·)
  return (sorted[k / 2]!, (h₁ - h₀) / k)

def main (args : List String) : IO Unit := do
  let k := (args.head? >>= String.toNat?).getD 11
  let errorType := args[1]?.getD "simple"
  IO.println s!"errors={errorType}"
  IO.println "records,bytes,parseit_us,parser_us,parseit_allocs,parser_allocs"
  let (f₁, f₂) : (String → Bool) × (String → Bool) :=
    if errorType == "trivial" then (BenchParseIt.JSONT.validate, BenchParser.JSONT.validate)
    else (BenchParseIt.JSON.validate, BenchParser.JSON.validate)
  for n in [100, 1000, 10000, 50000] do
    let s := genJSON n
    -- warm up
    discard <| timeRuns 1 f₁ s
    discard <| timeRuns 1 f₂ s
    let (t₁, a₁) ← timeRuns k f₁ s
    let (t₂, a₂) ← timeRuns k f₂ s
    IO.println s!"{n},{s.utf8ByteSize},{t₁},{t₂},{a₁},{a₂}"
