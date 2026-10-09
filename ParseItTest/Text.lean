import ParseIt

open ParseIt ParseIt.Char Std

abbrev E := Error.Basic CharIterator

/-- Render the outcome of running `p` on `s`. -/
def parseStr {α} [Repr α] (s : String) (p : Parser E CharIterator Char α) : String :=
  match p.parseString s with
  | .ok x => s!"ok {repr x}"
  | .error e => s!"error at {e.pos.byteIdx}"

-- character classes
#guard parseStr "a" (char 'a') == "ok 'a'"
#guard parseStr "b" (char 'a') == "error at 0"
#guard parseStr "let x" (string "let" <* space) == "ok \"let\""
#guard parseStr "lex" (string "let") == "error at 2"
#guard parseStr "\r\nx" (eol *> anyToken) == "ok 'x'"
#guard parseStr "\nx" (eol *> anyToken) == "ok 'x'"
#guard parseStr "Ab9_" (takeMany ASCII.alphanum) == "ok #['A', 'b', '9']"
#guard parseStr " \t\nx" (dropMany ASCII.whitespace *> ASCII.lowercase) == "ok 'x'"
#guard parseStr "f" (ASCII.hexDigit) == "ok 15"
#guard parseStr "G" (ASCII.hexDigit) == "error at 0"
#guard parseStr "7" (ASCII.octDigit) == "ok 7"
#guard parseStr "8" (ASCII.octDigit) == "error at 0"

-- multibyte characters: positions are byte offsets
#guard parseStr "∀x" (anyToken *> char 'y') == "error at 3"

-- numbers
#guard parseStr "12345" ASCII.parseNat == "ok 12345"
#guard parseStr "0x1F" (ASCII.parseNat (decimalOnly := false)) == "ok 31"
#guard parseStr "0b101" (ASCII.parseNat (decimalOnly := false)) == "ok 5"
#guard parseStr "017" (ASCII.parseNat (decimalOnly := false)) == "ok 15"
#guard parseStr "0" (ASCII.parseNat (decimalOnly := false)) == "ok 0"
-- long numbers span several digit chunks
#guard let s := String.join (List.replicate 13 "1234567890"); parseStr s ASCII.parseNat == s!"ok {s.toNat!}"
#guard let s := "00" ++ String.join (List.replicate 7 "9"); parseStr s ASCII.parseNat == "ok 9999999"
#guard parseStr ("0x" ++ String.join (List.replicate 9 "fF")) (ASCII.parseNat (decimalOnly := false)) ==
  s!"ok {2 ^ 72 - 1}"
#guard parseStr ("0b" ++ String.join (List.replicate 130 "1")) (ASCII.parseNat (decimalOnly := false)) ==
  s!"ok {2 ^ 130 - 1}"
#guard parseStr ("0" ++ String.join (List.replicate 45 "7")) (ASCII.parseNat (decimalOnly := false)) ==
  s!"ok {2 ^ 135 - 1}"
#guard parseStr ("1." ++ String.join (List.replicate 40 "0") ++ "1e40") (ASCII.parseScientific Float) ==
  s!"ok {repr (1e40 : Float)}"
#guard parseStr "-42" ASCII.parseInt == "ok -42"
#guard parseStr "+42" ASCII.parseInt == "ok 42"
#guard parseStr "1.5e2" (ASCII.parseScientific Float) == "ok 150.000000"
#guard parseStr "-0.25" ASCII.parseFloat == "ok -0.250000"
#guard parseStr "." (ASCII.parseScientific Float) == "error at 1"

-- README example from lean4-parser: sum of sign-separated integers; `foldl` stops before `+x`
def parseSum : Parser E CharIterator Char Int :=
  foldl (· + ·) 0 ASCII.parseInt <* endOfInput

#guard parseStr "11-1+2-3+33" parseSum == "ok 42"
#guard parseStr "11-1+x" parseSum == "error at 4"

-- captured text is a view into the input
#guard (match Parser.parseString (ε := E) (captureSlice (takeMany ASCII.alpha)) "abc123" with
  | .ok (_, s) => s.copy
  | .error _ => "") == "abc"

-- bits, least significant first
#guard (Parser.parseBitVec (ε := Error.Basic BitIterator) (takeMany (token true)) (0b0111#5)
  |>.toOption) == some #[true, true, true]
#guard (Parser.parseBitVec (ε := Error.Basic BitIterator) (take 3 anyToken <* endOfInput)
  (0b101#4) |>.toOption) == none
#guard (Parser.parseBitVec (ε := Error.Basic BitIterator) (count anyToken) (0#0) |>.toOption) ==
  some 0

-- bytes, arrays and lists
#guard (Parser.parseByteArray (ε := Error.Basic ByteIterator) (takeMany (token 0x61))
  "aab".toUTF8 |>.toOption) == some #[0x61, 0x61]
#guard (Parser.parseArray (ε := Error.Trivial) (count (token 1)) #[1, 1, 2] |>.toOption) ==
  some 2
#guard (Parser.parseVector (ε := Error.Trivial) (take 2 anyToken <* endOfInput) #v['a', 'b']
  |>.toOption) == some #['a', 'b']
#guard (Parser.parseList (ε := Error.Trivial) (sepBy (token 0) anyToken) [1, 0, 2, 0, 3]
  |>.toOption) == some #[1, 2, 3]

-- core's `String.Slice.chars` iterator
def word {ε ι} [Iterator ι Id Char] [Iterators.Finite ι Id] [Error ε ι Char] :
    Parser ε ι Char (Array Char) :=
  takeMany1 ASCII.alpha <* endOfInput

#guard (Parser.parseChars "abc".toSlice word
  (ε := Error.Basic (SliceChars "abc".toSlice))).toOption == some #['a', 'b', 'c']
#guard (match Parser.parseChars "ab1".toSlice word
    (ε := Error.Basic (SliceChars "ab1".toSlice)) with
  | .error e => e.pos.byteIdx == 2 && e.token == some '1'
  | .ok _ => false)
#guard (Parser.parseChars "é∀x".toSlice (takeMany anyToken (ε := Error.Trivial))).toOption ==
  some #['é', '∀', 'x']
