import ParseIt

/-! The examples from `TUTORIAL.md`. Keep the two in sync. -/

namespace Tutorial

open ParseIt ParseIt.Char

/-! ## Your first parser -/

abbrev P := Parser (Error.Basic CharIterator) CharIterator Char

def hello : P String := string "hello"

#guard (hello.parseString "hello world" |>.toOption) == some "hello"
#guard (hello.parseString "help" |>.toOption) == none

/-! ## Sequencing -/

def pair : P (Nat × Nat) := do
  let x ← ASCII.parseNat
  discard <| char ','
  let y ← ASCII.parseNat
  return (x, y)

def pair' : P (Nat × Nat) :=
  Prod.mk <$> ASCII.parseNat <* char ',' <*> ASCII.parseNat

#guard (pair.parseString "12,34" |>.toOption) == some (12, 34)
#guard (pair'.parseString "12,34" |>.toOption) == some (12, 34)

/-! ## Alternatives and backtracking -/

def keyword : P String := string "let" <|> string "lex"

#guard (keyword.parseString "lex" |>.toOption) == some "lex"

def sign : P Int := first [char '+' *> pure 1, char '-' *> pure (-1), pure 1]

#guard (sign.parseString "-" |>.toOption) == some (-1)
#guard (sign.parseString "7" |>.toOption) == some 1

/-! ## Repetition -/

def word : P String := do
  let c ← ASCII.alpha
  foldl String.push c.toString ASCII.alpha

def words : P (Array String) := sepBy (char ' ') word

#guard (words.parseString "parse it now" |>.toOption) == some #["parse", "it", "now"]

def digitSum : P Nat := foldl (fun n (d : Fin 10) => n + d) 0 ASCII.digit

#guard (digitSum.parseString "1234" |>.toOption) == some 10

def maybeAs : P (Array (Option Char)) := takeMany (option? (char 'a'))

#guard (maybeAs.parseString "aab" |>.toOption) == some #[some 'a', some 'a', none]

/-! ## A calculator -/

def ws : P Unit := dropMany ASCII.whitespace

def lexeme {α} (p : P α) : P α := p <* ws

def symbol (c : Char) : P Char := lexeme (char c)

def number : P Int := lexeme (Int.ofNat <$> ASCII.parseNat)

def addOp : P (Int → Int → Int) :=
  first [symbol '+' *> pure (· + ·), symbol '-' *> pure (· - ·)]

def mulOp : P (Int → Int → Int) :=
  symbol '*' *> pure (· * ·)

instance {α} : Inhabited (P α) := ⟨throwUnexpected⟩

mutual

partial def expr : P Int := do
  foldlP (fun x op => op x <$> term) (← term) addOp

partial def term : P Int := do
  foldlP (fun x op => op x <$> factor) (← factor) mulOp

partial def factor : P Int :=
  first [
    number,
    symbol '(' *> expr <* symbol ')',
    symbol '-' *> Int.neg <$> factor]

end

def calculate (s : String) : Except String Int :=
  match (ws *> expr <* endOfInput).parseString s with
  | .ok n => .ok n
  | .error e => .error s!"unexpected input at byte {e.pos.byteIdx}"

#guard (calculate "1 + 2 * 3").toOption == some 7
#guard (calculate " (1 + 2) * 3 ").toOption == some 9
#guard (calculate "2 * -(3 - 10)").toOption == some 14
#guard (calculate "10 - 4 - 3").toOption == some 3

/-! ## Errors -/

def calcError (s : String) : String :=
  match calculate s with
  | .ok _ => ""
  | .error msg => msg

#guard calcError "1 + 2 x" == "unexpected input at byte 6"
#guard calcError "1 + )" == "unexpected input at byte 2"

/-! ## Positions and captured text -/

def numberSpan : P (Nat × Nat) := do
  let (_, start, stop) ← withSpan number
  return (start.byteIdx, stop.byteIdx)

#guard (numberSpan.parseString "42  + 1" |>.toOption) == some (0, 4)

def ident : P String := lexeme do
  let (_, s) ← captureSlice (ASCII.alpha *> dropMany ASCII.alphanum)
  return s.copy

#guard (ident.parseString "x1 = 2" |>.toOption) == some "x1"

/-! ## Other inputs -/

inductive Tok where
  | num (n : Nat)
  | plus
deriving BEq

abbrev TokP := Parser Error.Trivial (Std.Iterators.Types.ArrayIterator Tok) Tok

def num : TokP Nat := tokenMap fun
  | .num n => some n
  | _ => none

def sum : TokP Nat := do
  let ns ← sepBy1 (token Tok.plus) num
  return ns.foldl (· + ·) 0

#guard (sum.parseArray #[.num 1, .plus, .num 2, .plus, .num 3] |>.toOption) == some 6

end Tutorial
