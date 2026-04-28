/-
  Thales/Parser/Lexer.lean
  Stateful lexer for JavaScript parsing
-/
import Thales.Parser.Token
import Thales.Parser.ExpectError

namespace Thales.Parser

open Thales.AST

/-- Lexer state -/
structure LexerState where
  input : String
  chars : Array Char  -- precomputed for O(1) character access
  pos : Nat  -- character index
  line : Nat
  column : Nat
  /-- True when we expect an expression (regex possible), false when expecting operator -/
  expectExpr : Bool
  /-- Collected `@thales-expect-error` directives, in source order.
      `appliesToLine` is filled in when the next non-comment, non-blank
      code line is encountered (or left 0 if EOF reaches first). -/
  directives : Array ExpectErrorDirective := #[]
  /-- Directives from the most recently scanned JSDoc `/** ... */` block.
      Reset to empty each time a new JSDoc block is scanned.
      The parser reads this when building an `annotatedFuncDecl` node. -/
  lastJSDoc : JSDocDirectives := {}
  deriving Repr

/-- Initialize lexer state from input string -/
def LexerState.init (input : String) : LexerState :=
  { input, chars := input.toList.toArray, pos := 0, line := 1, column := 0,
    expectExpr := true, directives := #[], lastJSDoc := {} }

/-- Check if we're at end of input -/
def LexerState.atEnd (s : LexerState) : Bool := s.pos >= s.chars.size

/-- Get character at position (returns default for out of bounds) -/
def LexerState.getCharAt (s : LexerState) (pos : Nat) : Char :=
  s.chars.getD pos '\x00'

/-- Peek at current character without advancing -/
def LexerState.peek (s : LexerState) : Option Char :=
  if s.atEnd then none else some (s.getCharAt s.pos)

/-- Peek at character at offset from current position -/
def LexerState.peekAt (s : LexerState) (offset : Nat) : Option Char :=
  let idx := s.pos + offset
  if idx >= s.input.length then none else some (s.getCharAt idx)

/-- Advance by one character -/
def LexerState.advance (s : LexerState) : LexerState :=
  if s.atEnd then s
  else
    let c := s.getCharAt s.pos
    if c == '\n' then
      { s with pos := s.pos + 1, line := s.line + 1, column := 0 }
    else
      { s with pos := s.pos + 1, column := s.column + 1 }

/-- Get current position as Position -/
def LexerState.getPosition (s : LexerState) : Position :=
  { line := s.line, column := s.column }

/-- Extract substring from position to current -/
def LexerState.extractFrom (s : LexerState) (startPos : Nat) : String :=
  String.ofList (s.chars.extract startPos s.pos).toList

/-- Result type for lexer operations -/
abbrev LexerResult (α : Type) := Except String α

/-- Check if character is a digit -/
def isDigit (c : Char) : Bool := c >= '0' && c <= '9'

/-- Check if character is a hex digit -/
def isHexDigit (c : Char) : Bool :=
  isDigit c || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')

/-- Check if character is an octal digit -/
def isOctalDigit (c : Char) : Bool := c >= '0' && c <= '7'

/-- Check if character is a binary digit -/
def isBinaryDigit (c : Char) : Bool := c == '0' || c == '1'

/-- Permissive approximation of Unicode ID_Start: any non-ASCII codepoint
    that isn't Unicode whitespace or punctuation/symbol-block. -/
def isUnicodeLetter (c : Char) : Bool :=
  c.isAlpha ||
  (c.toNat >= 0x80 &&
    c != '\u00A0' && c != '\u1680' &&
    !(c.toNat >= 0x2000 && c.toNat <= 0x200A) &&
    c != '\u2028' && c != '\u2029' && c != '\u202F' &&
    c != '\u205F' && c != '\u3000' && c != '\uFEFF' &&
    !(c.toNat >= 0x2010 && c.toNat <= 0x2027) &&
    !(c.toNat >= 0x2030 && c.toNat <= 0x205E) &&
    !(c.toNat >= 0x2190 && c.toNat <= 0x23FF) &&
    !(c.toNat >= 0x2500 && c.toNat <= 0x27FF) &&
    !(c.toNat >= 0xFE30 && c.toNat <= 0xFE4F) &&
    !(c.toNat >= 0xFE50 && c.toNat <= 0xFE6F))

/-- Check if character can start an identifier -/
def isIdentifierStart (c : Char) : Bool :=
  c.isAlpha || c == '_' || c == '$' || isUnicodeLetter c

/-- Check if character can continue an identifier (incl. combining marks, ZWNJ, ZWJ). -/
def isIdentifierPart (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '$' || isUnicodeLetter c ||
  (c.toNat >= 0x0300 && c.toNat <= 0x036F) ||
  c.toNat == 0x200C || c.toNat == 0x200D

/-- Whitespace per ES2015+ (ASCII + Unicode space chars + line/paragraph separators + BOM). -/
def isWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == '\x0B' || c == '\x0C' ||
  c == '\u00A0' || c == '\u1680' ||
  (c.toNat >= 0x2000 && c.toNat <= 0x200A) ||
  c == '\u2028' || c == '\u2029' || c == '\u202F' ||
  c == '\u205F' || c == '\u3000' || c == '\uFEFF'

/-- Parse digits to a natural number -/
def parseDigitsToNat (s : String) : Nat :=
  s.foldl (fun acc c =>
    if isDigit c then acc * 10 + (c.toNat - '0'.toNat)
    else acc) 0

/-- Parse a string to Float -/
def parseFloat (s : String) : Option Float :=
  let clean := s.replace "_" ""
  if clean.isEmpty then none
  else
    let hasDecimal := clean.any (· == '.')
    let hasExp := clean.any (fun c => c == 'e' || c == 'E')

    if !hasDecimal && !hasExp then
      some (parseDigitsToNat clean).toFloat
    else if !hasExp then
      let parts := clean.splitOn "."
      match parts with
      | [intPart, fracPart] =>
        let intVal := (parseDigitsToNat intPart).toFloat
        let fracVal := (parseDigitsToNat fracPart).toFloat
        let fracDiv := Float.pow 10 fracPart.length.toFloat
        some (intVal + fracVal / fracDiv)
      | _ => none
    else
      let eParts := clean.toLower.splitOn "e"
      match eParts with
      | [base, exp] =>
        let baseVal :=
          let bparts := base.splitOn "."
          match bparts with
          | [intPart] => (parseDigitsToNat intPart).toFloat
          | [intPart, fracPart] =>
            let intVal := (parseDigitsToNat intPart).toFloat
            let fracVal := (parseDigitsToNat fracPart).toFloat
            let fracDiv := Float.pow 10 fracPart.length.toFloat
            intVal + fracVal / fracDiv
          | _ => 0.0
        let (neg, expDigits) :=
          if exp.startsWith "-" then (true, exp.drop 1)
          else if exp.startsWith "+" then (false, exp.drop 1)
          else (false, exp)
        let expVal := (parseDigitsToNat expDigits.toString).toFloat
        let mult := Float.pow 10 expVal
        if neg then some (baseVal / mult) else some (baseVal * mult)
      | _ => none

/-- Skip to end of line -/
partial def skipToEndOfLine (s : LexerState) : LexerState :=
  if s.atEnd then s
  else
    let c := s.getCharAt s.pos
    if c == '\n' then s.advance
    else skipToEndOfLine s.advance

/-- Advance to end-of-line (newline char or EOF) without consuming the newline. -/
partial def advanceToEOL (s : LexerState) : LexerState :=
  if s.atEnd then s
  else if s.getCharAt s.pos == '\n' then s
  else advanceToEOL s.advance

/-- Read a line comment whose `//` has already been consumed. Captures the
    comment body for `@thales-expect-error` directive classification, then
    advances past the trailing newline (if any). -/
def skipLineCommentCapturing (s : LexerState) : LexerState :=
  let startPos := s.pos
  let startLine := s.line
  let atEol := advanceToEOL s
  let content := atEol.extractFrom startPos
  let directives' :=
    match ExpectError.parseDirectiveContent content with
    | .strict code =>
      atEol.directives.push
        { directiveLine := startLine, appliesToLine := 0, expectedCode := code, malformed := false }
    | .malformed =>
      atEol.directives.push
        { directiveLine := startLine, appliesToLine := 0, expectedCode := none, malformed := true }
    | .notADirective => atEol.directives
  let afterNewline :=
    if atEol.atEnd then atEol else atEol.advance
  { afterNewline with directives := directives' }

/-- Skip block comment, collecting its text content.
    `s` is positioned at the character immediately after `/ *`.
    Returns the state after `* /` and the raw body text. -/
partial def skipBlockCommentCapturing (s : LexerState) (acc : List Char) :
    Option (LexerState × String) :=
  if s.atEnd then none
  else
    let c := s.getCharAt s.pos
    if c == '*' then
      match s.peekAt 1 with
      | some '/' => some (s.advance.advance, String.ofList acc.reverse)
      | _ => skipBlockCommentCapturing s.advance (c :: acc)
    else skipBlockCommentCapturing s.advance (c :: acc)

/-- Skip whitespace and comments -/
partial def skipWhitespaceAndComments (s : LexerState) : LexerState :=
  if s.atEnd then s
  else
    let c := s.getCharAt s.pos
    if isWhitespace c then
      skipWhitespaceAndComments s.advance
    else if c == '/' then
      match s.peekAt 1 with
      | some '/' => skipWhitespaceAndComments (skipLineCommentCapturing s.advance.advance)
      | some '*' =>
        -- Detect JSDoc: `/**` (third char is also `*`)
        let isJSDoc := s.peekAt 2 == some '*'
        -- Skip past `/*`; for JSDoc also past the leading `*`
        let bodyStart := if isJSDoc then s.advance.advance.advance else s.advance.advance
        match skipBlockCommentCapturing bodyStart [] with
        | some (s', body) =>
          let s'' :=
            if isJSDoc then
              { s' with lastJSDoc := JSDoc.parseJSDocBlock body }
            else s'
          skipWhitespaceAndComments s''
        | none => s
      | _ => s
    else s

/-- Parse digits with a predicate -/
partial def parseDigits (s : LexerState) (pred : Char → Bool) : LexerState :=
  if s.atEnd then s
  else
    let c := s.getCharAt s.pos
    if pred c || c == '_' then parseDigits s.advance pred
    else s

/-- Convert hex string to Nat -/
def hexToNat (s : String) : Option Nat :=
  let clean := s.replace "_" ""
  if clean.isEmpty then none
  else
    let rec go : List Char → Nat → Option Nat
      | [], acc => some acc
      | c :: rest, acc =>
        if c >= '0' && c <= '9' then go rest (acc * 16 + (c.toNat - '0'.toNat))
        else if c >= 'a' && c <= 'f' then go rest (acc * 16 + (c.toNat - 'a'.toNat + 10))
        else if c >= 'A' && c <= 'F' then go rest (acc * 16 + (c.toNat - 'A'.toNat + 10))
        else none
    go clean.toList 0

/-- Convert binary string to Nat -/
def binaryToNat (s : String) : Option Nat :=
  let clean := s.replace "_" ""
  if clean.isEmpty then none
  else
    let rec go : List Char → Nat → Option Nat
      | [], acc => some acc
      | c :: rest, acc =>
        if c == '0' || c == '1' then go rest (acc * 2 + (c.toNat - '0'.toNat))
        else none
    go clean.toList 0

/-- Convert octal string to Nat -/
def octalToNat (s : String) : Option Nat :=
  let clean := s.replace "_" ""
  if clean.isEmpty then none
  else
    let rec go : List Char → Nat → Option Nat
      | [], acc => some acc
      | c :: rest, acc =>
        if c >= '0' && c <= '7' then go rest (acc * 8 + (c.toNat - '0'.toNat))
        else none
    go clean.toList 0

/-- Number type info -/
inductive NumberKind where
  | decimal
  | hex
  | binary
  | octal
  deriving Repr, BEq

/-- Parse a number literal -/
def parseNumber (s : LexerState) : LexerResult (LexerState × Token) := do
  let startPos := s.getPosition
  let startCharPos := s.pos

  -- Check for hex, binary, or octal prefix
  let (s', numKind) : LexerState × NumberKind :=
    if s.peek == some '0' then
      match s.peekAt 1 with
      | some 'x' | some 'X' => (s.advance.advance, .hex)
      | some 'b' | some 'B' => (s.advance.advance, .binary)
      | some 'o' | some 'O' => (s.advance.advance, .octal)
      | _ => (s, .decimal)
    else (s, .decimal)

  let prefixCharPos := s'.pos

  let parseDigitFn := match numKind with
    | .hex => isHexDigit
    | .binary => isBinaryDigit
    | .octal => isOctalDigit
    | .decimal => isDigit

  let isSpecial := numKind != .decimal

  -- Parse the integer part
  let s'' := parseDigits s' parseDigitFn

  -- Check for BigInt suffix 'n' (no decimals/exponents allowed)
  let isBigInt := s''.peek == some 'n'
  if isBigInt then
    let s''' := s''.advance
    let raw := s'''.extractFrom startCharPos
    let endPos := s'''.getPosition
    -- Parse the integer value
    let value : Int :=
      if isSpecial then
        let numStr := s''.extractFrom prefixCharPos
        let converted := match numKind with
          | .hex => hexToNat numStr
          | .binary => binaryToNat numStr
          | .octal => octalToNat numStr
          | .decimal => none
        match converted with
        | some v => v
        | none => 0
      else
        (parseDigitsToNat ((s''.extractFrom startCharPos).replace "_" ""))
    let token : Token := {
      kind := .bigint value
      raw := raw
      pos := startPos
      endPos := endPos
    }
    return ({ s''' with expectExpr := false }, token)

  -- Parse decimal part (only for regular numbers, not BigInt)
  let s''' :=
    if !isSpecial && s''.peek == some '.' && (match s''.peekAt 1 with | some c => isDigit c | none => false) then
      parseDigits s''.advance isDigit
    else s''

  -- Parse exponent (only for regular decimal numbers)
  let s'''' :=
    if !isSpecial && (s'''.peek == some 'e' || s'''.peek == some 'E') then
      let s2 := s'''.advance
      let s3 := if s2.peek == some '+' || s2.peek == some '-' then s2.advance else s2
      parseDigits s3 isDigit
    else s'''

  let raw := s''''.extractFrom startCharPos
  let endPos := s''''.getPosition

  -- Parse the number value
  let value :=
    if isSpecial then
      let numStr := s''''.extractFrom prefixCharPos
      let converted := match numKind with
        | .hex => hexToNat numStr
        | .binary => binaryToNat numStr
        | .octal => octalToNat numStr
        | .decimal => none
      match converted with
      | some v => v.toFloat
      | none => 0.0
    else
      match parseFloat raw with
      | some v => v
      | none => 0.0

  let token : Token := {
    kind := .number value
    raw := raw
    pos := startPos
    endPos := endPos
  }

  return ({ s'''' with expectExpr := false }, token)

/-- Parse hex escape \xHH -/
def parseHexEscapeN (s : LexerState) (count : Nat) : Option (LexerState × Char) :=
  let rec go (s : LexerState) (n : Nat) (value : Nat) : Option (LexerState × Char) :=
    match n with
    | 0 => some (s, Char.ofNat value)
    | n' + 1 =>
      match s.peek with
      | some c =>
        if c >= '0' && c <= '9' then
          go s.advance n' (value * 16 + (c.toNat - '0'.toNat))
        else if c >= 'a' && c <= 'f' then
          go s.advance n' (value * 16 + (c.toNat - 'a'.toNat + 10))
        else if c >= 'A' && c <= 'F' then
          go s.advance n' (value * 16 + (c.toNat - 'A'.toNat + 10))
        else none
      | none => none
  go s count 0

/-- Parse unicode escape \u{H+} or \uHHHH -/
partial def parseUnicodeEscape (s : LexerState) : Option (LexerState × Char) :=
  if s.peek == some '{' then
    let rec go (s : LexerState) (value : Nat) : Option (LexerState × Char) :=
      match s.peek with
      | some '}' => some (s.advance, Char.ofNat value)
      | some c =>
        if c >= '0' && c <= '9' then
          go s.advance (value * 16 + (c.toNat - '0'.toNat))
        else if c >= 'a' && c <= 'f' then
          go s.advance (value * 16 + (c.toNat - 'a'.toNat + 10))
        else if c >= 'A' && c <= 'F' then
          go s.advance (value * 16 + (c.toNat - 'A'.toNat + 10))
        else none
      | none => none
    go s.advance 0
  else
    parseHexEscapeN s 4

/-- Parse string content -/
partial def parseStringContent (s : LexerState) (quote : Char) (acc : String) : LexerResult (LexerState × String) := do
  if s.atEnd then throw "Unterminated string"
  let c := s.getCharAt s.pos
  if c == quote then return (s, acc)
  else if c == '\\' then
    let s' := s.advance
    if s'.atEnd then throw "Unterminated string escape"
    let escaped := s'.getCharAt s'.pos
    let (s'', charOpt) := match escaped with
      | 'n' => (s'.advance, some '\n')
      | 'r' => (s'.advance, some '\r')
      | 't' => (s'.advance, some '\t')
      | '\\' => (s'.advance, some '\\')
      | '\'' => (s'.advance, some '\'')
      | '"' => (s'.advance, some '"')
      | '0' => (s'.advance, some '\x00')
      | 'b' => (s'.advance, some '\x08')
      | 'f' => (s'.advance, some '\x0C')
      | 'v' => (s'.advance, some '\x0B')
      | '\n' => (s'.advance, none)
      | 'x' =>
        match parseHexEscapeN s'.advance 2 with
        | some (s'', char) => (s'', some char)
        | none => (s'.advance, some escaped)
      | 'u' =>
        match parseUnicodeEscape s'.advance with
        | some (s'', char) => (s'', some char)
        | none => (s'.advance, some escaped)
      | _ => (s'.advance, some escaped)
    match charOpt with
    | some char => parseStringContent s'' quote (acc.push char)
    | none => parseStringContent s'' quote acc
  else if c == '\n' then
    throw "Unterminated string - newline in string literal"
  else
    parseStringContent s.advance quote (acc.push c)

/-- Parse a string literal -/
def parseString (s : LexerState) (quote : Char) : LexerResult (LexerState × Token) := do
  let startPos := s.getPosition
  let startCharPos := s.pos
  let s' := s.advance

  let (s'', content) ← parseStringContent s' quote ""

  if s''.atEnd then
    throw s!"Unterminated string literal at line {startPos.line}"

  let s''' := s''.advance
  let raw := s'''.extractFrom startCharPos
  let endPos := s'''.getPosition

  let token : Token := {
    kind := .string content
    raw := raw
    pos := startPos
    endPos := endPos
  }

  return ({ s''' with expectExpr := false }, token)

/-- Parse template literal content until ` or ${ -/
partial def parseTemplateContent (s : LexerState) (cooked : String) (raw : String)
    : LexerResult (LexerState × String × String × Bool) := do
  -- Returns (state, cooked, raw, foundInterpolation)
  if s.atEnd then throw "Unterminated template literal"
  let c := s.getCharAt s.pos
  if c == '`' then
    return (s, cooked, raw, false)  -- End of template
  else if c == '$' && s.peekAt 1 == some '{' then
    return (s, cooked, raw, true)   -- Found ${
  else if c == '\\' then
    let s' := s.advance
    if s'.atEnd then throw "Unterminated template escape"
    let escaped := s'.getCharAt s'.pos
    let (s'', cookedChar, rawStr) := match escaped with
      | 'n' => (s'.advance, some '\n', "\\n")
      | 'r' => (s'.advance, some '\r', "\\r")
      | 't' => (s'.advance, some '\t', "\\t")
      | '\\' => (s'.advance, some '\\', "\\\\")
      | '`' => (s'.advance, some '`', "\\`")
      | '$' => (s'.advance, some '$', "\\$")
      | '0' => (s'.advance, some '\x00', "\\0")
      | '\n' => (s'.advance, none, "\\\n")
      | 'x' =>
        match parseHexEscapeN s'.advance 2 with
        | some (s'', char) => (s'', some char, s''.extractFrom s.pos)
        | none => (s'.advance, some escaped, "\\")
      | 'u' =>
        match parseUnicodeEscape s'.advance with
        | some (s'', char) => (s'', some char, s''.extractFrom s.pos)
        | none => (s'.advance, some escaped, "\\")
      | _ => (s'.advance, some escaped, s!"\\" ++ escaped.toString)
    let cooked' := match cookedChar with
      | some ch => cooked.push ch
      | none => cooked
    parseTemplateContent s'' cooked' (raw ++ rawStr)
  else
    parseTemplateContent s.advance (cooked.push c) (raw.push c)

/-- Parse a template literal starting from backtick
    isHead: true if this is the start of a template (after `)
            false if this is after } in an interpolation -/
def parseTemplate (s : LexerState) (isHead : Bool) : LexerResult (LexerState × Token) := do
  let startPos := s.getPosition
  let startCharPos := s.pos
  let s' := s.advance  -- Skip ` or }

  let (s'', cooked, raw, hasInterpolation) ← parseTemplateContent s' "" ""

  if hasInterpolation then
    -- Skip the ${
    let s''' := s''.advance.advance
    let fullRaw := s'''.extractFrom startCharPos
    let endPos := s'''.getPosition
    let kind := if isHead then TokenKind.templateHead cooked raw else TokenKind.templateMiddle cooked raw
    let token : Token := {
      kind := kind
      raw := fullRaw
      pos := startPos
      endPos := endPos
    }
    return ({ s''' with expectExpr := true }, token)
  else
    -- End of template, skip closing `
    let s''' := s''.advance
    let fullRaw := s'''.extractFrom startCharPos
    let endPos := s'''.getPosition
    let kind := if isHead then TokenKind.templateNoSub cooked raw else TokenKind.templateTail cooked raw
    let token : Token := {
      kind := kind
      raw := fullRaw
      pos := startPos
      endPos := endPos
    }
    return ({ s''' with expectExpr := false }, token)

/-- Parse identifier characters with unicode escape support
    Returns (new state, accumulated identifier name, had unicode escape) -/
partial def parseIdentCharsWithUnicode (s : LexerState) (acc : String) (hadEscape : Bool := false) : LexerState × String × Bool :=
  if s.atEnd then (s, acc, hadEscape)
  else
    let c := s.getCharAt s.pos
    if c == '\\' && s.peekAt 1 == some 'u' then
      -- Unicode escape in identifier: \uXXXX or \u{XXXX}
      let s' := s.advance.advance  -- Skip \u
      match parseUnicodeEscape s' with
      | some (s'', char) =>
        -- Verify the character is valid for identifier continuation
        if isIdentifierPart char then
          parseIdentCharsWithUnicode s'' (acc.push char) true
        else
          (s, acc, hadEscape)  -- Invalid identifier char, stop here
      | none => (s, acc, hadEscape)  -- Invalid escape, stop
    else if isIdentifierPart c then
      parseIdentCharsWithUnicode s.advance (acc.push c) hadEscape
    else
      (s, acc, hadEscape)

/-- Parse identifier start character with unicode escape support -/
partial def parseIdentStartWithUnicode (s : LexerState) : Option (LexerState × Char) :=
  if s.atEnd then none
  else
    let c := s.getCharAt s.pos
    if c == '\\' && s.peekAt 1 == some 'u' then
      -- Unicode escape at start of identifier
      let s' := s.advance.advance  -- Skip \u
      match parseUnicodeEscape s' with
      | some (s'', char) =>
        if isIdentifierStart char then some (s'', char)
        else none
      | none => none
    else if isIdentifierStart c then
      some (s.advance, c)
    else
      none

/-- Parse an identifier or keyword -/
def parseIdentifier (s : LexerState) : LexerResult (LexerState × Token) := do
  let startPos := s.getPosition
  let startCharPos := s.pos

  -- Check for unicode escape at start
  let c := s.getCharAt s.pos
  let (s', name, hadEscape) :=
    if c == '\\' && s.peekAt 1 == some 'u' then
      -- Unicode escape at start
      match parseIdentStartWithUnicode s with
      | some (sAfterStart, startChar) =>
        let (sFinal, restChars, restHadEscape) := parseIdentCharsWithUnicode sAfterStart ""
        (sFinal, String.singleton startChar ++ restChars, true || restHadEscape)
      | none =>
        -- Invalid escape, fall back to regular parsing
        let sFinal := s
        (sFinal, "", false)
    else
      -- Regular identifier start
      let (sFinal, ident, hadEscape) := parseIdentCharsWithUnicode s ""
      (sFinal, ident, hadEscape)

  if name.isEmpty then
    throw s!"Expected identifier at line {startPos.line}"

  let endPos := s'.getPosition

  -- An identifier with a unicode escape is never a keyword (e.g. `l\u0065t` ≠ `let`).
  let kind := if hadEscape then .identifier name
    else match stringToKeyword name with
    | some kw => kw
    | none => .identifier name

  let expectExpr := match kind with
    | .return | .throw | .new | .typeof | .void | .delete | .await | .yield => true
    | .in | .instanceof => true
    | .else => true
    | .case | .default => true
    | _ => false

  let token : Token := {
    kind := kind
    raw := s'.extractFrom startCharPos  -- Keep the raw form with escapes
    pos := startPos
    endPos := endPos
  }

  return ({ s' with expectExpr }, token)

/-- Parse a private identifier #name -/
def parsePrivateIdentifier (s : LexerState) : LexerResult (LexerState × Token) := do
  let startPos := s.getPosition
  let startCharPos := s.pos
  let s' := s.advance  -- Skip #

  -- Must be followed by a valid identifier start character
  if s'.atEnd then throw "Unexpected end of input after '#'"
  let c := s'.getCharAt s'.pos

  -- Check for Unicode escape at identifier start (like parseIdentifier does)
  let (s'', name) ←
    if c == '\\' && s'.peekAt 1 == some 'u' then
      -- Unicode escape at start
      match parseIdentStartWithUnicode s' with
      | some (sAfterStart, startChar) =>
        let (sFinal, restChars, _) := parseIdentCharsWithUnicode sAfterStart ""
        pure (sFinal, String.singleton startChar ++ restChars)
      | none =>
        throw s!"Invalid private identifier at line {startPos.line}"
    else if isIdentifierStart c then
      -- Regular identifier start
      let (sFinal, ident, _) := parseIdentCharsWithUnicode s' ""
      pure (sFinal, ident)
    else
      throw s!"Invalid private identifier at line {startPos.line}"

  if name.isEmpty then
    throw s!"Invalid private identifier at line {startPos.line}"

  let raw := s''.extractFrom startCharPos
  let endPos := s''.getPosition

  let token : Token := {
    kind := .privateIdentifier name
    raw := raw
    pos := startPos
    endPos := endPos
  }

  return ({ s'' with expectExpr := false }, token)

/-- Parse regex pattern content until closing /
    Returns (state, pattern, inCharClass) where inCharClass tracks if we're inside [...] -/
partial def parseRegexContent (s : LexerState) (acc : String) (inCharClass : Bool)
    : LexerResult (LexerState × String) := do
  if s.atEnd then throw "Unterminated regex literal"
  let c := s.getCharAt s.pos
  if c == '\\' then
    -- Escape sequence - consume next char too
    if s.advance.atEnd then throw "Unterminated regex escape"
    let escaped := s.getCharAt (s.pos + 1)
    parseRegexContent s.advance.advance (acc.push c |>.push escaped) inCharClass
  else if c == '[' && !inCharClass then
    -- Entering character class
    parseRegexContent s.advance (acc.push c) true
  else if c == ']' && inCharClass then
    -- Exiting character class
    parseRegexContent s.advance (acc.push c) false
  else if c == '/' && !inCharClass then
    -- End of pattern
    return (s, acc)
  else if c == '\n' then
    throw "Unterminated regex literal - newline in pattern"
  else
    parseRegexContent s.advance (acc.push c) inCharClass

/-- Parse regex flags after closing / -/
partial def parseRegexFlags (s : LexerState) (acc : String) : LexerState × String :=
  if s.atEnd then (s, acc)
  else
    let c := s.getCharAt s.pos
    -- Valid regex flags: g, i, m, s, u, y, d
    if c == 'g' || c == 'i' || c == 'm' || c == 's' || c == 'u' || c == 'y' || c == 'd' then
      parseRegexFlags s.advance (acc.push c)
    else
      (s, acc)

/-- Parse a regex literal /pattern/flags -/
def parseRegex (s : LexerState) : LexerResult (LexerState × Token) := do
  let startPos := s.getPosition
  let startCharPos := s.pos
  let s' := s.advance  -- Skip opening /

  let (s'', pattern) ← parseRegexContent s' "" false
  let s''' := s''.advance  -- Skip closing /
  let (s'''', flags) := parseRegexFlags s''' ""

  let raw := s''''.extractFrom startCharPos
  let endPos := s''''.getPosition

  let token : Token := {
    kind := .regex pattern flags
    raw := raw
    pos := startPos
    endPos := endPos
  }

  return ({ s'''' with expectExpr := false }, token)

/-- Parse a punctuator or operator -/
def parsePunctuator (s : LexerState) : LexerResult (LexerState × Token) := do
  let startPos := s.getPosition
  let c := s.getCharAt s.pos

  let (s', kind, raw) ← match c with
    | '.' =>
      if s.peekAt 1 == some '.' && s.peekAt 2 == some '.' then
        pure (s.advance.advance.advance, TokenKind.ellipsis, "...")
      else
        pure (s.advance, TokenKind.dot, ".")

    | '+' =>
      match s.peekAt 1 with
      | some '+' => pure (s.advance.advance, TokenKind.plusplus, "++")
      | some '=' => pure (s.advance.advance, TokenKind.pluseq, "+=")
      | _ => pure (s.advance, TokenKind.plus, "+")

    | '-' =>
      match s.peekAt 1 with
      | some '-' => pure (s.advance.advance, TokenKind.minusminus, "--")
      | some '=' => pure (s.advance.advance, TokenKind.minuseq, "-=")
      | _ => pure (s.advance, TokenKind.minus, "-")

    | '*' =>
      match s.peekAt 1 with
      | some '*' =>
        if s.peekAt 2 == some '=' then
          pure (s.advance.advance.advance, TokenKind.starstareq, "**=")
        else
          pure (s.advance.advance, TokenKind.starstar, "**")
      | some '=' => pure (s.advance.advance, TokenKind.stareq, "*=")
      | _ => pure (s.advance, TokenKind.star, "*")

    | '/' =>
      match s.peekAt 1 with
      | some '=' => pure (s.advance.advance, TokenKind.slasheq, "/=")
      | _ => pure (s.advance, TokenKind.slash, "/")

    | '%' =>
      if s.peekAt 1 == some '=' then
        pure (s.advance.advance, TokenKind.percenteq, "%=")
      else
        pure (s.advance, TokenKind.percent, "%")

    | '<' =>
      match s.peekAt 1 with
      | some '<' =>
        if s.peekAt 2 == some '=' then
          pure (s.advance.advance.advance, TokenKind.ltlteq, "<<=")
        else
          pure (s.advance.advance, TokenKind.ltlt, "<<")
      | some '=' => pure (s.advance.advance, TokenKind.leq, "<=")
      | _ => pure (s.advance, TokenKind.lt, "<")

    | '>' =>
      match s.peekAt 1 with
      | some '>' =>
        match s.peekAt 2 with
        | some '>' =>
          if s.peekAt 3 == some '=' then
            pure (s.advance.advance.advance.advance, TokenKind.gtgtgteq, ">>>=")
          else
            pure (s.advance.advance.advance, TokenKind.gtgtgt, ">>>")
        | some '=' => pure (s.advance.advance.advance, TokenKind.gtgteq, ">>=")
        | _ => pure (s.advance.advance, TokenKind.gtgt, ">>")
      | some '=' => pure (s.advance.advance, TokenKind.geq, ">=")
      | _ => pure (s.advance, TokenKind.gt, ">")

    | '=' =>
      match s.peekAt 1 with
      | some '=' =>
        if s.peekAt 2 == some '=' then
          pure (s.advance.advance.advance, TokenKind.seq, "===")
        else
          pure (s.advance.advance, TokenKind.eq, "==")
      | some '>' => pure (s.advance.advance, TokenKind.arrow, "=>")
      | _ => pure (s.advance, TokenKind.assign, "=")

    | '!' =>
      match s.peekAt 1 with
      | some '=' =>
        if s.peekAt 2 == some '=' then
          pure (s.advance.advance.advance, TokenKind.sneq, "!==")
        else
          pure (s.advance.advance, TokenKind.neq, "!=")
      | _ => pure (s.advance, TokenKind.bang, "!")

    | '&' =>
      match s.peekAt 1 with
      | some '&' =>
        if s.peekAt 2 == some '=' then
          pure (s.advance.advance.advance, TokenKind.ampampeq, "&&=")
        else
          pure (s.advance.advance, TokenKind.ampamp, "&&")
      | some '=' => pure (s.advance.advance, TokenKind.ampeq, "&=")
      | _ => pure (s.advance, TokenKind.amp, "&")

    | '|' =>
      match s.peekAt 1 with
      | some '|' =>
        if s.peekAt 2 == some '=' then
          pure (s.advance.advance.advance, TokenKind.pipepipeeq, "||=")
        else
          pure (s.advance.advance, TokenKind.pipepipe, "||")
      | some '=' => pure (s.advance.advance, TokenKind.pipeeq, "|=")
      | _ => pure (s.advance, TokenKind.pipe, "|")

    | '^' =>
      if s.peekAt 1 == some '=' then
        pure (s.advance.advance, TokenKind.careteq, "^=")
      else
        pure (s.advance, TokenKind.caret, "^")

    | '~' => pure (s.advance, TokenKind.tilde, "~")

    | '?' =>
      match s.peekAt 1 with
      | some '?' =>
        if s.peekAt 2 == some '=' then
          pure (s.advance.advance.advance, TokenKind.questionquestioneq, "??=")
        else
          pure (s.advance.advance, TokenKind.questionquestion, "??")
      | some '.' =>
        -- ?. is optional chaining, but ?.digit should be ? followed by .digit
        let isDigitNext := match s.peekAt 2 with
          | some c => isDigit c
          | none => false
        if isDigitNext then
          pure (s.advance, TokenKind.question, "?")
        else
          pure (s.advance.advance, TokenKind.questiondot, "?.")
      | _ => pure (s.advance, TokenKind.question, "?")

    | '(' => pure (s.advance, TokenKind.lparen, "(")
    | ')' => pure (s.advance, TokenKind.rparen, ")")
    | '{' => pure (s.advance, TokenKind.lbrace, "{")
    | '}' => pure (s.advance, TokenKind.rbrace, "}")
    | '[' => pure (s.advance, TokenKind.lbracket, "[")
    | ']' => pure (s.advance, TokenKind.rbracket, "]")
    | ';' => pure (s.advance, TokenKind.semicolon, ";")
    | ',' => pure (s.advance, TokenKind.comma, ",")
    | ':' => pure (s.advance, TokenKind.colon, ":")

    | _ => throw s!"Unexpected character: '{c}' at line {s.line}, column {s.column}"

  let expectExpr := match kind with
    | .lparen | .lbrace | .lbracket | .comma | .semicolon | .colon
    | .question | .questionquestion
    | .plus | .minus | .star | .slash | .percent | .starstar
    | .lt | .gt | .leq | .geq | .eq | .neq | .seq | .sneq
    | .ltlt | .gtgt | .gtgtgt
    | .amp | .pipe | .caret | .tilde | .bang
    | .ampamp | .pipepipe
    | .assign | .pluseq | .minuseq | .stareq | .slasheq | .percenteq
    | .starstareq | .ltlteq | .gtgteq | .gtgtgteq | .pipeeq | .careteq
    | .ampeq | .pipepipeeq | .ampampeq | .questionquestioneq
    | .arrow | .ellipsis => true
    | .rparen | .rbrace | .rbracket | .dot | .questiondot
    | .plusplus | .minusminus => false
    | _ => s.expectExpr

  let endPos := s'.getPosition
  let token : Token := {
    kind := kind
    raw := raw
    pos := startPos
    endPos := endPos
  }

  return ({ s' with expectExpr }, token)

/-- Get the next token from the lexer -/
def nextToken (s : LexerState) : LexerResult (LexerState × Token) := do
  let s0 := skipWhitespaceAndComments s
  -- Fill in appliesToLine for any pending directives whose applied line
  -- hasn't been resolved yet. The first non-whitespace/non-comment token's
  -- line is that line. Malformed directives keep 0 (they never suppress).
  let s' :=
    if s0.atEnd then s0
    else
      let currentLine := s0.line
      { s0 with
        directives := s0.directives.map fun d =>
          if d.appliesToLine == 0 && !d.malformed then
            { d with appliesToLine := currentLine }
          else d }

  if s'.atEnd then
    let pos := s'.getPosition
    return (s', { kind := .eof, raw := "", pos := pos, endPos := pos })

  let c := s'.getCharAt s'.pos

  if isDigit c then
    parseNumber s'
  else if c == '"' || c == '\'' then
    parseString s' c
  else if c == '`' then
    parseTemplate s' true
  else if c == '/' && s'.expectExpr then
    -- When expecting an expression, / starts a regex literal
    -- (Otherwise, it's division operator handled by parsePunctuator)
    -- But first check it's not // or /* (comments - already stripped by skipWhitespaceAndComments)
    match s'.peekAt 1 with
    | some '/' | some '*' =>
      -- This shouldn't happen since comments are stripped, but handle gracefully
      parsePunctuator s'
    | _ => parseRegex s'
  else if c == '#' then
    -- Private identifier: #name
    parsePrivateIdentifier s'
  else if isIdentifierStart c then
    parseIdentifier s'
  else if c == '\\' && s'.peekAt 1 == some 'u' then
    -- Unicode escape starting an identifier: \u0041 or \u{41}
    parseIdentifier s'
  else
    parsePunctuator s'

/-- Continue parsing after } in template interpolation
    Expects current position to be at } -/
def nextTemplateToken (s : LexerState) : LexerResult (LexerState × Token) := do
  let s0 := skipWhitespaceAndComments s
  let s' :=
    if s0.atEnd then s0
    else
      let currentLine := s0.line
      { s0 with
        directives := s0.directives.map fun d =>
          if d.appliesToLine == 0 && !d.malformed then
            { d with appliesToLine := currentLine }
          else d }
  if s'.atEnd then throw "Unexpected end of template"
  let c := s'.getCharAt s'.pos
  if c != '}' then throw s!"Expected '}' in template, got '{c}'"
  -- Parse the template continuation (isHead=false because we're after })
  parseTemplate s' false

end Thales.Parser
