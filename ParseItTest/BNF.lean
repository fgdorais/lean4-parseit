import ParseItExamples.BNF

-- the BNF parser parses its own syntax, and printing it back gives the same text
#guard match BNF.parse BNF.bnf with
  | .ok stx => toString stx == BNF.bnf
  | .error _ => false

#guard match BNF.parse "<a> ::= 'x' | <b>\n<b> ::= 'y'\n" with
  | .ok stx => toString stx == "<a> ::= 'x' | <b>\n<b> ::= 'y'\n"
  | .error _ => false

-- malformed rules are errors
#guard (BNF.parse "<a> ::= 'x'").toOption.isNone
#guard (BNF.parse "<a> 'x'\n").toOption.isNone
#guard (BNF.parse "<a> ::= 'x\n").toOption.isNone
#guard (BNF.parse "a ::= 'x'\n").toOption.isNone
