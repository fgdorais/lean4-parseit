import ParseIt

open ParseIt ParseIt.Char Std Unicode ScalarArray

/-- The sum of sign-separated integers, as in the README. -/
def sumOf (ι : Type) [Iterator ι Id Char] [Iterators.Finite ι Id] [HasPos ι Char]
    [LE (HasPos.Pos ι)] [DecidableLE (HasPos.Pos ι)] : Parser (Error.Basic ι) ι Char Int :=
  foldl (· + ·) 0 ASCII.parseInt <* endOfInput

/-- Characters other than `!`, up to the end of the input. -/
def untilBang (ι : Type) [Iterator ι Id Char] [Iterators.Finite ι Id] [HasPos ι Char]
    [LE (HasPos.Pos ι)] [DecidableLE (HasPos.Pos ι)] :
    Parser (Error.Basic ι) ι Char (Array Char) :=
  takeMany (tokenFilter (· != '!')) <* endOfInput

/-- The result of a parse, as a string. -/
def show? {ε α : Type} [ToString ε] [ToString α] : Except ε α → String
  | .ok x => s!"ok {x}"
  | .error e => s!"error {e}"

/-! UTF-16 -/

#guard show? ((sumOf UTF16Iterator).parseUTF16 (UTF16.encode "11-1+2-3+33")) == "ok 42"
#guard show? ((sumOf UTF16Iterator).parseUTF16 (UTF16.encode "11-1+x")) ==
  "error unexpected input '+' at 4"
-- Decoding stops at the unpaired surrogate, which is reported there.
#guard show? ((sumOf UTF16Iterator).parseUTF16 [0x31, 0x32, 0xD800, 0x33].toUInt16Array) ==
  "error unexpected input at 2"
-- A parse that fails before the unpaired surrogate reports its own error.
#guard show? ((sumOf UTF16Iterator).parseUTF16 [0x78, 0x31, 0xD800].toUInt16Array) ==
  "error unexpected input 'x' at 0"
-- A parse that stops before the unpaired surrogate succeeds.
#guard show? (Parser.parseUTF16
  (anyToken : Parser (Error.Basic UTF16Iterator) UTF16Iterator Char Char)
  [0x31, 0x32, 0xD800].toUInt16Array) == "ok 1"
-- Lossy decoding yields U+FFFD, which the parser rejects.
#guard show? ((sumOf UTF16Iterator).parseDecoded
  (UTF16.decodeIterLossy [0x31, 0x32, 0xD800, 0x33].toUInt16Array.iter)) ==
  "error unexpected input '�' at 2"
-- Positions are indices in the array.
#guard show? ((sumOf UTF16Iterator).parseUTF16 ((UTF16.encode "x12")[1...*])) == "ok 12"
#guard show? ((sumOf UTF16Iterator).parseUTF16 ((UTF16.encode "x1y")[1...*])) ==
  "error unexpected input 'y' at 2"

/-! UTF-8 -/

#guard show? ((sumOf UTF8Iterator).parseUTF8 "40+2".toUTF8) == "ok 42"
-- Positions are byte offsets.
#guard show? ((sumOf UTF8Iterator).parseUTF8 "é1".toUTF8) == "error unexpected input 'é' at 0"
-- After multi-byte characters: byte offsets for UTF-8, code unit indices for UTF-16.
#guard show? ((untilBang UTF8Iterator).parseUTF8 "日本!".toUTF8) ==
  "error unexpected input '!' at 6"
#guard show? ((untilBang UTF16Iterator).parseUTF16 (UTF16.encode "日😀!")) ==
  "error unexpected input '!' at 3"
#guard show? ((sumOf UTF8Iterator).parseUTF8 [0x31, 0x32, 0xFF].toByteArray) ==
  "error unexpected input at 2"
#guard show? ((sumOf UTF8Iterator).parseUTF8 [0x31, 0xE2, 0x88].toByteArray) ==
  "error unexpected input at 1"

/-! UTF-32 -/

#guard show? ((sumOf UTF32Iterator).parseUTF32 (UTF32.encode "6*7")) ==
  "error unexpected input '*' at 1"
#guard show? ((sumOf UTF32Iterator).parseUTF32 [0x31, 0x110000].toUInt32Array) ==
  "error unexpected input at 1"

/-! Messages -/

/-- The sum of sign-separated integers, with simple errors. -/
def sumSimple : Parser (Error.Simple UTF16Iterator) UTF16Iterator Char Int :=
  foldl (· + ·) 0 ASCII.parseInt <* endOfInput

#guard (show? (sumSimple.parseUTF16 [0x31, 0xDC00].toUInt16Array)).endsWith
  "unexpected input at 1; unpaired surrogate at 1"
-- A failed parse keeps its error and gets a message about the ill-formed input.
#guard (show? (sumSimple.parseUTF16 [0x78, 0x31, 0xD800].toUInt16Array)).endsWith
  "; unpaired surrogate at 2"

/-! Going on after ill-formed input -/

/-- Integers separated by spaces, and each ill-formed input with its position. -/
def intsOrIll (ι : Type) [Iterator ι Id Char] [Iterators.Finite ι Id] [HasPos ι Char]
    [LE (HasPos.Pos ι)] [DecidableLE (HasPos.Pos ι)] (item : Parser (Error.Basic ι) ι Char String) :
    Parser (Error.Basic ι) ι Char (Array String) :=
  takeMany (dropMany space *> ((toString <$> ASCII.parseInt) <|> item)) <* dropMany space
    <* endOfInput

def ill8 : Parser (Error.Basic UTF8Iterator) UTF8Iterator Char String := do
  let pos ← getPos
  let k ← illFormed
  return s!"<{k} at {pos}>"

def ill16 : Parser (Error.Basic UTF16Iterator) UTF16Iterator Char String := do
  let pos ← getPos
  let k ← illFormed
  return s!"<{k} at {pos}>"

#guard show? ((intsOrIll UTF8Iterator ill8).parseUTF8 "12 34".toUTF8) == "ok #[12, 34]"
#guard show? ((intsOrIll UTF8Iterator ill8).parseUTF8
  [0x31, 0x20, 0xFF, 0x32, 0xC0, 0xAF].toByteArray) ==
  "ok #[1, <ill-formed UTF-8 at 2>, 2, <ill-formed UTF-8 at 4>, <ill-formed UTF-8 at 5>]"
-- A maximal subpart is consumed as a whole.
#guard show? ((intsOrIll UTF8Iterator ill8).parseUTF8 [0x37, 0xE2, 0x88, 0x38].toByteArray) ==
  "ok #[7, <ill-formed UTF-8 at 1>, 8]"
#guard show? ((intsOrIll UTF16Iterator ill16).parseUTF16 [0x31, 0xD800, 0x32].toUInt16Array) ==
  "ok #[1, <unpaired surrogate at 1>, 2]"
-- Syntax errors are still errors.
#guard show? ((intsOrIll UTF8Iterator ill8).parseUTF8 "1 x".toUTF8) ==
  "error unexpected input 'x' at 2"
-- `illFormed` fails at well-formed input and at the end of the input.
#guard show? (Parser.parseUTF8 (illFormed : Parser (Error.Basic UTF8Iterator) UTF8Iterator Char _)
  "a".toUTF8) == "error unexpected input 'a' at 0"
#guard show? (Parser.parseUTF8 (illFormed : Parser (Error.Basic UTF8Iterator) UTF8Iterator Char _)
  ByteArray.empty) == "error unexpected input at 0"
