import ParseIt

open ParseIt ParseIt.Char Std

/-- Run `p` on `s` and return the result, if any. -/
def parseU {α} (s : String) (p : Parser Error.Trivial CharIterator Char α) : Option α :=
  p.parseString s |>.toOption

#guard parseU "é" Unicode.alpha == some 'é'
#guard parseU "1" Unicode.alpha == none
#guard parseU "Ωx" (Unicode.uppercase *> Unicode.lowercase) == some 'x'
#guard parseU "∀" Unicode.math == some '∀'
#guard parseU "　" Unicode.whitespace == some '　'
#guard parseU "٣" Unicode.digit == some 3
#guard parseU "²" Unicode.digit == none
#guard parseU "Ｆ" Unicode.hexDigit == some 15
#guard parseU "日本語" (takeMany Unicode.GeneralCategory.otherLetter) == some #['日', '本', '語']
#guard parseU "a_b" (Unicode.alpha *> Unicode.GeneralCategory.connectorPunctuation) == some '_'
#guard parseU "€" (Unicode.parseGeneralCategory .Sc) == some '€'

-- scripts
#guard parseU "α" (Unicode.parseScript (.ofAbbrev! "Grek")) == some 'α'
#guard parseU "a" (Unicode.parseScript (.ofAbbrev! "Grek")) == none
-- U+0951 has script Zinh but is used with Devanagari, Bengali and others
#guard parseU "\u0951" (Unicode.parseScript (.ofAbbrev! "Deva")) == none
#guard parseU "\u0951" (Unicode.parseScriptExt (.ofAbbrev! "Deva")) == some '\u0951'
#guard parseU "\u0951" (Unicode.parseScriptExt (.ofAbbrev! "Beng")) == some '\u0951'
-- U+00B7 MIDDLE DOT has script Zyyy, but its extensions are explicit scripts
#guard parseU "·" (Unicode.parseScript (.ofAbbrev! "Zyyy")) == some '·'
#guard parseU "·" (Unicode.parseScriptExt (.ofAbbrev! "Zyyy")) == none
#guard parseU "·" (Unicode.parseScriptExt (.ofAbbrev! "Grek")) == some '·'

-- binary and special properties
#guard parseU "\uFDD0" Unicode.noncharacter == some '\uFDD0'
#guard parseU "a" Unicode.noncharacter == none
#guard parseU "\u00AD" Unicode.defaultIgnorable == some '\u00AD'
#guard parseU "\u0378" Unicode.assigned == none
#guard parseU "\u0378" Unicode.GeneralCategory.unassigned == some '\u0378'
#guard parseU "\uE000" Unicode.assigned == some '\uE000'
#guard parseU "~" Unicode.ascii == some '~'
#guard parseU "é" Unicode.ascii == none
#guard parseU "\u200D" Unicode.joinControl == some '\u200D'
-- Alphabetic includes letter numbers and other alphabetic marks, not just letters
#guard parseU "Ⅻ" Unicode.alpha == some 'Ⅻ'
#guard parseU "Ⅻ" Unicode.GeneralCategory.letter == none

-- general categories used by compatibility properties
#guard parseU "٣" Unicode.GeneralCategory.decimalNumber == some '٣'
#guard parseU "²" Unicode.GeneralCategory.decimalNumber == none
#guard parseU "¿" Unicode.GeneralCategory.punctuation == some '¿'
#guard parseU "\n" Unicode.whitespace == some '\n'
#guard parseU "\u007F" Unicode.GeneralCategory.control == some '\u007F'


-- case-insensitive matching
#guard parseU "Σ" (Unicode.charCaseInsensitive 'σ') == some 'Σ'
#guard parseU "ς" (Unicode.charCaseInsensitive 'σ') == some 'ς'
#guard parseU "ParseIT" (Unicode.stringCaseInsensitive "parseit") == some "ParseIT"
#guard parseU "parsex" (Unicode.stringCaseInsensitive "parseit") == none
-- full case folding: one input character may match several pattern characters
#guard parseU "Straße!" (Unicode.stringCaseInsensitive "strasse") == some "Straße"
#guard parseU "STRASSE" (Unicode.stringCaseInsensitive "strasse") == some "STRASSE"
#guard parseU "ﬁle" (Unicode.stringCaseInsensitive "file") == some "ﬁle"
#guard parseU "Strase" (Unicode.stringCaseInsensitive "strasse") == none
#guard parseU "ß" (Unicode.stringCaseInsensitive "s") == none
#guard parseU "x" (Unicode.stringCaseInsensitive "") == some ""
