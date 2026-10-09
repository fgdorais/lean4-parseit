import ParseIt

open ParseIt Std

/-- Value of a successful parse, if any. -/
def ParseIt.Result.value? {ε ι τ α : Type} [Iterator ι Id τ] {it : Iter (α := ι) τ} :
    Result ε it α → Option α
  | .ok _ _ x => some x
  | .error _ => none

/-- Run a trivial-error parser on the characters of a string. -/
def parse {α} (s : String)
    (p : ∀ {ι} [Iterator ι Id Char] [Iterators.Finite ι Id], Parser Error.Trivial ι Char α) :
    Option α :=
  (p.run s.toSlice.chars).value?

#guard parse "aaab" (takeMany (token 'a')) == some #['a', 'a', 'a']
#guard parse "" (takeMany (token 'a')) == some #[]
#guard parse "abc" (count anyToken) == some 3
#guard parse "ab" (token 'b') == none
#guard parse "ab" (token 'a' *> token 'b' <* endOfInput) == some 'b'
#guard parse "ab" (token 'b' <|> token 'a') == some 'a'
-- an empty match ends the repetition instead of looping forever
#guard parse "xyz" (count (pure ())) == some 1
#guard parse "aab" (count ((token 'a' *> pure ()) <|> pure ())) == some 3
