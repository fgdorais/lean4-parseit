import ParseItTest.Util

open ParseIt Std

-- lookAhead and notFollowedBy consume nothing
#guard parseArray #['a', 'b'] Basic (lookAhead (token 'a')) == "ok 'a' at 0"
#guard parseArray #['a', 'b'] Basic (token 'a' *> notFollowedBy (token 'a')) == "ok () at 1"
#guard parseArray #['a', 'a'] Basic (token 'a' *> notFollowedBy (token 'a')) ==
  "error: unexpected input at 1"

-- option family
#guard parseArray #['a'] Basic (option? (token 'b')) == "ok none at 0"
#guard parseArray #['b'] Basic (option? (token 'b')) == "ok some 'b' at 1"
#guard parseArray #['x'] Basic (optionD (token 'b') (pure 'z')) == "ok 'z' at 0"
#guard parseArray #['x'] Basic (test (token 'x')) == "ok true at 1"
#guard parseArray #['x'] Basic (test (token 'y')) == "ok false at 0"
#guard parseArray #['x'] Basic (optional (token 'y') *> token 'x') == "ok 'x' at 1"

-- `<|>` backtracks and `Basic` keeps the furthest error
#guard parseArray #['a', 'c'] Basic ((token 'a' *> token 'b') <|> token 'x') ==
  "error: unexpected input 'c' at 1"
#guard parseArray #['a', 'c'] Basic ((token 'a' *> token 'b') <|> (token 'a' *> token 'c')) ==
  "ok 'c' at 2"

-- first
#guard parseArray #['c'] Basic (first [token 'a', token 'b', token 'c']) == "ok 'c' at 1"
#guard parseArray #['d'] Basic (first [token 'a', token 'b']) ==
  "error: unexpected input 'd' at 0"
#guard parseArray #['d'] Basic (first (α := Char) []) == "error: unexpected input at 0"

-- `Simple` records every alternative, and messages
#guard parseArray #['d'] Simple (token 'a' <|> token 'b') ==
  "error: unexpected input 'd' at 0 or unexpected input 'd' at 0"
#guard parseArray #['d'] Simple (withErrorMessage "expected a" (token 'a')) ==
  "error: unexpected input 'd' at 0; expected a at 0"
#guard parseArray #['d'] Simple (first [token 'a', token 'b']) ==
  "error: unexpected input 'd' at 0 or unexpected input 'd' at 0"

-- positions
#guard parseArray #['a', 'b'] Basic (token 'a' *> getPos) == "ok 1 at 1"
#guard parseArray #['a', 'b', 'c'] Basic (token 'a' *> withSpan (takeMany (token 'b'))) ==
  "ok (#['b'], 1, 2) at 2"
#guard parseArray #['a', 'x'] Basic (withSpan (token 'a' *> token 'b')) ==
  "error: unexpected input 'x' at 1"

-- token sequences
#guard parseArray #['a', 'b', 'c'] Basic (tokenArray #['a', 'b']) == "ok #['a', 'b'] at 2"
#guard parseArray #['a', 'x'] Basic (tokenArray #['a', 'b']) == "error: unexpected input 'x' at 1"
#guard parseArray #['a', 'b'] Basic (tokenList ['a', 'b'] <* endOfInput) == "ok ['a', 'b'] at 2"
#guard parseArray #['a'] Basic (tokenArray #[]) == "ok #[] at 0"
