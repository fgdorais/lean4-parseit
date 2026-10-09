import ParseItTest.Util

open ParseIt Std

-- folds
#guard parseBasic "abc" (foldl (fun s c => s.push c) "" anyToken) == "ok \"abc\" at 3"
#guard parseBasic "123" (foldlP (fun n c => if c == '3' then throwUnexpected else pure (n + 1))
  0 anyToken) == "ok 2 at 2"
#guard parseBasic "abc" (foldr (fun c s => s.push c) anyToken (pure "")) == "ok \"cba\" at 3"
#guard parseBasic "aab" (foldr List.cons (token 'a') (token 'b' *> pure [])) ==
  "ok ['a', 'a'] at 3"
-- foldr retries with fewer occurrences when `q` fails
#guard parseBasic "aa" (foldr List.cons (token 'a') (token 'a' *> pure [])) == "ok ['a'] at 2"

-- take family
#guard parseBasic "aaab" (take 2 (token 'a')) == "ok #['a', 'a'] at 2"
#guard parseBasic "ab" (take 2 (token 'a')) == "error: unexpected input 'b' at 1"
#guard parseBasic "aaab" (takeUpTo 2 (token 'a')) == "ok #['a', 'a'] at 2"
#guard parseBasic "ab" (takeUpTo 2 (token 'a')) == "ok #['a'] at 1"
#guard parseBasic "aaab" (takeMany (token 'a')) == "ok #['a', 'a', 'a'] at 3"
#guard parseBasic "b" (takeMany1 (token 'a')) == "error: unexpected input 'b' at 0"
#guard parseBasic "aab" (takeManyN 2 (token 'a')) == "ok #['a', 'a'] at 2"
#guard parseBasic "ab" (takeManyN 2 (token 'a')) == "error: unexpected input 'b' at 1"
#guard parseBasic "aab" (takeUntil (token 'b') anyToken) == "ok (#['a', 'a'], 'b') at 3"
#guard parseBasic "aa" (takeUntil (token 'b') anyToken) == "error: unexpected input at 2"
-- `takeUntil` with a parser that consumes nothing reports the error from `stop`
#guard parseBasic "a" (takeUntil (token 'b') (pure 'x')) == "error: unexpected input 'a' at 0"

-- drop family
#guard parseBasic "aab" (drop 2 (token 'a') *> anyToken) == "ok 'b' at 3"
#guard parseBasic "ab" (dropUpTo 3 (token 'a') *> anyToken) == "ok 'b' at 2"
#guard parseBasic "aab" (dropMany (token 'a') *> anyToken) == "ok 'b' at 3"
#guard parseBasic "b" (dropMany1 (token 'a')) == "error: unexpected input 'b' at 0"
#guard parseBasic "aaab" (dropManyN 2 (token 'a') *> anyToken) == "ok 'b' at 4"
#guard parseBasic "xyz." (dropUntil (token '.') anyToken) == "ok '.' at 4"

-- count family
#guard parseBasic "aaab" (count (token 'a')) == "ok 3 at 3"
#guard parseBasic "aaab" (countUpTo 2 (token 'a')) == "ok 2 at 2"
#guard parseBasic "ab;" (countUntil (token ';') anyToken) == "ok (2, ';') at 3"

-- endBy family
#guard parseBasic "a;a;" (endBy (token ';') (token 'a')) == "ok #['a', 'a'] at 4"
#guard parseBasic "a;a" (endBy (token ';') (token 'a')) == "ok #['a'] at 2"
#guard parseBasic "a;a" (endBy (token ';') (token 'a') (strict := true)) ==
  "error: unexpected input at 3"
#guard parseBasic "" (endBy1 (token ';') (token 'a')) == "error: unexpected input at 0"

-- sepBy family
#guard parseBasic "a,a,a" (sepBy (token ',') (token 'a')) == "ok #['a', 'a', 'a'] at 5"
#guard parseBasic "" (sepBy (token ',') (token 'a')) == "ok #[] at 0"
#guard parseBasic "a,a," (sepBy (token ',') (token 'a')) == "ok #['a', 'a'] at 3"
#guard parseBasic "a,a," (sepNoEndBy (token ',') (token 'a')) == "error: unexpected input at 4"
#guard parseBasic "a,a," (sepEndBy (token ',') (token 'a')) == "ok #['a', 'a'] at 4"
#guard parseBasic "b" (sepBy1 (token ',') (token 'a')) == "error: unexpected input 'b' at 0"
#guard parseBasic "a,a,b" (sepEndBy1 (token ',') (token 'a')) == "ok #['a', 'a'] at 4"
