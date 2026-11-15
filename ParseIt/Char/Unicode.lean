/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ParseIt.Char.Basic
public import UnicodeBasic

/-! # Unicode character parsers

Parsers for Unicode character properties, using the UnicodeBasic tables: general categories,
scripts and script extensions, binary properties, and case-insensitive matching.
-/

namespace ParseIt.Char.Unicode
open Std

variable {ε ι : Type} {m : Type → Type} [Iterator ι Id Char] [Iterators.Productive ι Id]
  [Error ε ι Char] [Monad m]

/-- Parse alphabetic character (Unicode property `Alphabetic`). -/
public def alpha : ParserT ε ι Char m Char :=
  withErrorMessage "expected alphabetic character" <|
    tokenFilter Unicode.isAlpha

/-- Parse lowercase character (Unicode property `Lowercase`). -/
public def lowercase : ParserT ε ι Char m Char :=
  withErrorMessage "expected lowercase letter" <|
    tokenFilter Unicode.isLowercase

/-- Parse math character (Unicode property `Math`). -/
public def math : ParserT ε ι Char m Char :=
  withErrorMessage "expected math symbol" <|
    tokenFilter Unicode.isMath

/-- Parse uppercase character (Unicode property `Uppercase`). -/
public def uppercase : ParserT ε ι Char m Char :=
  withErrorMessage "expected uppercase letter" <|
    tokenFilter Unicode.isUppercase

/-- Parse white space character (Unicode property `White_Space`). -/
public def whitespace : ParserT ε ι Char m Char :=
  withErrorMessage "expected whitespace" <|
    tokenFilter Unicode.isWhiteSpace

/--
Parse decimal digit character (general category Nd). Other digits, such as superscripts, are
rejected.
-/
public def digit : ParserT ε ι Char m (Fin 10) :=
  withErrorMessage "expected decimal digit" <|
    tokenMap fun c => if Unicode.isDecimal c then Unicode.getDigit? c else none

/-- Parse hexadecimal digit character. -/
public def hexDigit : ParserT ε ι Char m (Fin 16) :=
  withErrorMessage "expected hexadecimal digit" <|
    tokenMap Unicode.getHexDigit?

/-- Parse noncharacter code point (Unicode property `Noncharacter_Code_Point`). -/
public def noncharacter : ParserT ε ι Char m Char :=
  withErrorMessage "expected noncharacter code point" <|
    tokenFilter Unicode.isNoncharacterCodePoint

/-- Parse default ignorable code point (Unicode property `Default_Ignorable_Code_Point`). -/
public def defaultIgnorable : ParserT ε ι Char m Char :=
  withErrorMessage "expected default ignorable code point" <|
    tokenFilter Unicode.isDefaultIgnorableCodePoint

/-- Parse ASCII character, U+0000 to U+007F. -/
public def ascii : ParserT ε ι Char m Char :=
  withErrorMessage "expected ASCII character" <|
    tokenFilter fun c => c.val < 0x80

/-- Parse assigned character, any general category except Cn. -/
public def assigned : ParserT ε ι Char m Char :=
  withErrorMessage "expected assigned character" <|
    tokenFilter fun c => !Unicode.GeneralCategory.isUnassigned c

/-- Parse join control character, U+200C or U+200D (Unicode property `Join_Control`). -/
public def joinControl : ParserT ε ι Char m Char :=
  withErrorMessage "expected join control character" <|
    tokenFilter fun c => c == '\u200C' || c == '\u200D'

/-!
  ## Case-insensitive matching ##
-/

/--
`charCaseInsensitive c` accepts and returns a character that matches `c` under simple case folding
(Unicode property `Simple_Case_Folding`).
-/
public def charCaseInsensitive (c : Char) : ParserT ε ι Char m Char :=
  let f := Unicode.getCaseFoldingChar c
  withErrorMessage s!"expected {repr c} (case-insensitive)" <|
    tokenFilter fun t => Unicode.getCaseFoldingChar t == f

/--
`stringCaseInsensitive s` accepts input whose full case folding (Unicode property `Case_Folding`,
statuses C and F) equals `s`, and returns the input that matched. The pattern `s` is expected to be
case folded already, for example `"strasse"` matches `"Straße"` and `"STRASSE"`.
-/
public def stringCaseInsensitive (s : String) : ParserT ε ι Char m String :=
  withErrorMessage s!"expected {repr s} (case-insensitive)" <| loop s.utf8ByteSize s.toSlice ""
where
  /-- Match the folded characters `rest`, with fuel `n` bounding the number of input characters. -/
  loop : Nat → String.Slice → String → ParserT ε ι Char m String
    | 0, rest, acc => if rest.isEmpty then pure acc else throwUnexpected
    | n + 1, rest, acc =>
      if rest.isEmpty then pure acc else do
        let (c, rest) ← tokenMap fun c =>
          if c.val < 0x80 then
            -- ASCII fast path
            let f := if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.val + 0x20).toNat else c
            (rest.dropPrefix? f).map (c, ·)
          else
            Unicode.withCaseFolding c fun f fs =>
              match rest.dropPrefix? f, fs with
              | some rest, [] => some (c, rest)
              | some rest, fs =>
                (fs.foldlM (fun (r : String.Slice) f => r.dropPrefix? f) rest).map (c, ·)
              | none, _ => none
        loop n rest (acc.push c)

/-!
  ## Scripts ##
-/

/-- Parse character of script `sc` (Unicode property `Script`). -/
public def parseScript (sc : Unicode.Script) : ParserT ε ι Char m Char :=
  withErrorMessage s!"expected character of script {sc.toAbbrev}" <|
    tokenFilter (Unicode.getScript · == sc)

/--
Parse character commonly used with script `sc` (Unicode property `Script_Extensions`).

This differs from `parseScript sc`: for example, U+0951 DEVANAGARI STRESS SIGN UDATTA has script
`Zinh` (Inherited) but is accepted by `parseScriptExt` for `Deva`, `Beng` and others.
-/
public def parseScriptExt (sc : Unicode.Script) : ParserT ε ι Char m Char :=
  withErrorMessage s!"expected character used with script {sc.toAbbrev}" <|
    tokenFilter (sc ∈ Unicode.getScriptSet ·)

/-!
  ## General Category ##
-/

/-- Parse character from given general category. -/
public def parseGeneralCategory (category : Unicode.GC) : ParserT ε ι Char m Char :=
  withErrorMessage s!"expected character of general category {category}" <|
    tokenFilter (. ∈ category)

namespace GeneralCategory

/-- Parse letter (general category L). -/
public def letter : ParserT ε ι Char m Char :=
  withErrorMessage "expected letter (L)" <|
    tokenFilter Unicode.GeneralCategory.isLetter

/-- Parse cased letter (general category LC). -/
public def casedLetter : ParserT ε ι Char m Char :=
  withErrorMessage "expected cased letter (LC)" <|
    tokenFilter Unicode.GeneralCategory.isCasedLetter

/-- Parse lowercase letter (general category Ll). -/
public def lowercaseLetter : ParserT ε ι Char m Char :=
  withErrorMessage "expected lowercase letter (Ll)" <|
    tokenFilter Unicode.GeneralCategory.isLowercaseLetter

/-- Parse uppercase letter (general category Lu). -/
public def uppercaseLetter : ParserT ε ι Char m Char :=
  withErrorMessage "expected uppercase letter (Lu)" <|
    tokenFilter Unicode.GeneralCategory.isUppercaseLetter

/-- Parse titlecase letter (general category Lt). -/
public def titlecaseLetter : ParserT ε ι Char m Char :=
  withErrorMessage "expected titlecase letter (Lt)" <|
    tokenFilter Unicode.GeneralCategory.isTitlecaseLetter

/-- Parse other letter (general category Lm). -/
public def modifierLetter : ParserT ε ι Char m Char :=
  withErrorMessage "expected modifier letter (Lm)" <|
    tokenFilter Unicode.GeneralCategory.isModifierLetter

/-- Parse other letter (general category Lo). -/
public def otherLetter : ParserT ε ι Char m Char :=
  withErrorMessage "expected other letter (Lo)" <|
    tokenFilter Unicode.GeneralCategory.isOtherLetter

/-- Parse mark (general category M). -/
public def mark : ParserT ε ι Char m Char :=
  withErrorMessage "expected mark (M)" <|
    tokenFilter Unicode.GeneralCategory.isMark

/-- Parse spacing combining mark (general category Mc). -/
public def spacingMark : ParserT ε ι Char m Char :=
  withErrorMessage "expected spacing mark (Mc)" <|
    tokenFilter Unicode.GeneralCategory.isSpacingMark

/-- Parse nonspacing combining mark (general category Mn). -/
public def nonspacingMark : ParserT ε ι Char m Char :=
  withErrorMessage "expected nonspacing mark (Mn)" <|
    tokenFilter Unicode.GeneralCategory.isNonspacingMark

/-- Parse enclosing combining mark (general category Me). -/
public def enclosingMark : ParserT ε ι Char m Char :=
  withErrorMessage "expected enclosing mark (Me)" <|
    tokenFilter Unicode.GeneralCategory.isEnclosingMark

/-- Parse number (general category N). -/
public def number : ParserT ε ι Char m Char :=
  withErrorMessage "expected number (N)" <|
    tokenFilter Unicode.GeneralCategory.isNumber

/-- Parse decimal number (general category Nd). -/
public def decimalNumber : ParserT ε ι Char m Char :=
  withErrorMessage "expected decimal number (Nd)" <|
    tokenFilter Unicode.GeneralCategory.isDecimalNumber

/-- Parse letter number (general category Nl). -/
public def letterNumber : ParserT ε ι Char m Char :=
  withErrorMessage "expected letter number (Nl)" <|
    tokenFilter Unicode.GeneralCategory.isLetterNumber

/-- Parse other number (general category No). -/
public def otherNumber : ParserT ε ι Char m Char :=
  withErrorMessage "expected other number (No)" <|
    tokenFilter Unicode.GeneralCategory.isOtherNumber

/-- Parse punctuation (general category P). -/
public def punctuation : ParserT ε ι Char m Char :=
  withErrorMessage "expected punctuation (P)" <|
    tokenFilter Unicode.GeneralCategory.isPunctuation

/-- Parse connector punctuation (general category Pc). -/
public def connectorPunctuation : ParserT ε ι Char m Char :=
  withErrorMessage "expected connector punctuation (Pc)" <|
    tokenFilter Unicode.GeneralCategory.isConnectorPunctuation

/-- Parse dash punctuation (general category Pd). -/
public def dashPunctuation : ParserT ε ι Char m Char :=
  withErrorMessage "expected dash punctuation (Pd)" <|
    tokenFilter Unicode.GeneralCategory.isDashPunctuation

/-- Parse opening punctuation (general category Ps). -/
public def openPunctuation : ParserT ε ι Char m Char :=
  withErrorMessage "expected opening punctuation (Ps)" <|
    tokenFilter Unicode.GeneralCategory.isOpenPunctuation

/-- Parse closing punctuation (general category Pe). -/
public def closePunctuation : ParserT ε ι Char m Char :=
  withErrorMessage "expected opening punctuation (Pe)" <|
    tokenFilter Unicode.GeneralCategory.isClosePunctuation

/-- Parse initial punctuation (general category Pi). -/
public def initialPunctuation : ParserT ε ι Char m Char :=
  withErrorMessage "expected initial punctuation (Pi)" <|
    tokenFilter Unicode.GeneralCategory.isInitialPunctuation

/-- Parse final punctuation (general category Pf). -/
public def finalPunctuation : ParserT ε ι Char m Char :=
  withErrorMessage "expected final punctuation (Pf)" <|
    tokenFilter Unicode.GeneralCategory.isFinalPunctuation

/-- Parse other punctuation (general category Po). -/
public def otherPunctuation : ParserT ε ι Char m Char :=
  withErrorMessage "expected other punctuation (Po)" <|
    tokenFilter Unicode.GeneralCategory.isOtherPunctuation

/-- Parse symbol (general category S). -/
public def symbol : ParserT ε ι Char m Char :=
  withErrorMessage "expected symbol (S)" <|
    tokenFilter Unicode.GeneralCategory.isSymbol

/-- Parse math symbol (general category Sm). -/
public def mathSymbol : ParserT ε ι Char m Char :=
  withErrorMessage "expected math symbol (Sm)" <|
    tokenFilter Unicode.GeneralCategory.isMathSymbol

/-- Parse currency symbol (general category Sc). -/
public def currencySymbol : ParserT ε ι Char m Char :=
  withErrorMessage "expected currency symbol (Sc)" <|
    tokenFilter Unicode.GeneralCategory.isCurrencySymbol

/-- Parse modifier symbol (general category Sk). -/
public def modifierSymbol : ParserT ε ι Char m Char :=
  withErrorMessage "expected modifier symbol (Sk)" <|
    tokenFilter Unicode.GeneralCategory.isModifierSymbol

/-- Parse other symbol (general category So). -/
public def otherSymbol : ParserT ε ι Char m Char :=
  withErrorMessage "expected other symbol (So)" <|
    tokenFilter Unicode.GeneralCategory.isOtherSymbol

/-- Parse separator (general category Z). -/
public def separator : ParserT ε ι Char m Char :=
  withErrorMessage "expected separator (Z)" <|
    tokenFilter Unicode.GeneralCategory.isSeparator

/-- Parse space separator (general category Zs). -/
public def spaceSeparator : ParserT ε ι Char m Char :=
  withErrorMessage "expected space separator (Zs)" <|
    tokenFilter Unicode.GeneralCategory.isSpaceSeparator

/-- Parse line separator (general category Zl). -/
public def lineSeparator : ParserT ε ι Char m Char :=
  withErrorMessage "expected line separator (Zl)" <|
    tokenFilter Unicode.GeneralCategory.isLineSeparator

/-- Parse paragraph separator (general category Zp). -/
public def paragraphSeparator : ParserT ε ι Char m Char :=
  withErrorMessage "expected paragraph separator (Zp)" <|
    tokenFilter Unicode.GeneralCategory.isParagraphSeparator

/-- Parse other character (general category C). -/
public def other : ParserT ε ι Char m Char :=
  withErrorMessage "expected other character (C)" <|
    tokenFilter Unicode.GeneralCategory.isOther

/-- Parse control character (general category Cc). -/
public def control : ParserT ε ι Char m Char :=
  withErrorMessage "expected control character (Cc)" <|
    tokenFilter Unicode.GeneralCategory.isControl

/-- Parse format character (general category Cf). -/
public def format : ParserT ε ι Char m Char :=
  withErrorMessage "expected format character (Cf)" <|
    tokenFilter Unicode.GeneralCategory.isFormat

/-- Parse private-use character (general category Co). -/
public def privateUse : ParserT ε ι Char m Char :=
  withErrorMessage "expected private-use character (Co)" <|
    tokenFilter Unicode.GeneralCategory.isPrivateUse

/-- Parse unassigned code point (general category Cn). -/
public def unassigned : ParserT ε ι Char m Char :=
  withErrorMessage "expected unassigned code point (Cn)" <|
    tokenFilter Unicode.GeneralCategory.isUnassigned

end GeneralCategory

end ParseIt.Char.Unicode
