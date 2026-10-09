import ParseIt
import Std.Data.Iterators

open ParseIt Std

/-- Run a parser on an array and render the outcome. -/
def parseArray {α} [Repr α] (xs : Array Char) (ε)
    [Error ε (Iterators.Types.ArrayIterator Char) Char]
    [ToString ε] (p : Parser ε (Iterators.Types.ArrayIterator Char) Char α) : String :=
  match p.run xs.iter with
  | .ok rest _ x => s!"ok {repr x} at {rest.internalState.pos}"
  | .error e => s!"error: {e}"

abbrev Basic := Error.Basic (Iterators.Types.ArrayIterator Char)
abbrev Simple := Error.Simple (Iterators.Types.ArrayIterator Char)

/-- Run a parser with basic errors on the characters of `s`, as an array. -/
def parseBasic {α} [Repr α] (s : String)
    (p : Parser Basic (Iterators.Types.ArrayIterator Char) Char α) : String :=
  parseArray s.toList.toArray Basic p
