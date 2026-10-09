import ParseIt

/-! The example from `README.md`. Keep the two in sync. -/

namespace Readme

open ParseIt ParseIt.Char

/-- Parses a list of sign-separated integers (no spaces) and returns their sum. -/
def parseSum : Parser (Error.Basic CharIterator) CharIterator Char Int :=
  foldl (· + ·) 0 ASCII.parseInt <* endOfInput

#guard (parseSum.parseString "11-1+2-3+33" |>.toOption) == some 42

end Readme
