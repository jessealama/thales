/-
  Thales/Parser/ExpectError.lean
  `@thales-expect-error` directive type and grammar recognition.
  Also handles `@throws` and `@total` JSDoc directives.

  Lives in the Parser layer (not Emit) because directives are collected by
  the lexer alongside ordinary tokens. `SubsetCheck` consumes them later.
-/
import Thales.AST

namespace Thales.Parser

/-- A recognised `@thales-expect-error` directive attached to a line-comment. -/
structure ExpectErrorDirective where
  /-- 1-based source line of the `//` that started the directive comment. -/
  directiveLine : Nat
  /-- 1-based source line of the next non-comment, non-blank code line.
      0 means EOF was reached first. -/
  appliesToLine : Nat
  /-- Expected TH code digits (e.g. 1 for TH0001), or none for code-less form. -/
  expectedCode : Option Nat
  /-- Matched the loose prefix but not the strict grammar — fires TH9003. -/
  malformed : Bool
  deriving Repr, Inhabited, BEq

/-- Directives parsed from a JSDoc `/** ... */` block immediately preceding a
    function declaration. Collected by the lexer; read by the parser when
    building an `annotatedFuncDecl` node. -/
structure JSDocDirectives where
  /-- Throws annotation: `.absent` if no `@throws`; `.declared types` if any
      `@throws` directive appeared (types may be empty). -/
  throwsAnn : Thales.AST.ThrowsAnnotation := .absent
  /-- True iff `@total` appears in the block. -/
  total : Bool := false
  deriving Repr, Inhabited, BEq

namespace ExpectError

/-- Classification of a line-comment's content against the directive grammar.
    The content passed is the text *after* `//`, with leading/trailing
    whitespace included. -/
inductive DirectiveMatch where
  /-- Well-formed directive; optional expected code. -/
  | strict (expectedCode : Option Nat)
  /-- Matched loose prefix but failed strict — emits TH9003. -/
  | malformed
  /-- Not a directive; ordinary comment. -/
  | notADirective
  deriving Repr, BEq, DecidableEq

/-- Is this an ASCII space or tab? -/
private def isSpaceOrTab (c : Char) : Bool := c == ' ' || c == '\t'

/-- Strip leading ASCII space/tab. -/
private def ltrim (s : String) : String :=
  (s.toRawSubstring.dropWhile isSpaceOrTab).toString

/-- Strip trailing ASCII space/tab. -/
private def rtrim (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile isSpaceOrTab).reverse

/-- Parse exactly `TH` followed by exactly four digits. Returns the numeric
    value on success. -/
private def parseTHCode (s : String) : Option Nat :=
  if s.length = 6 && s.startsWith "TH" then
    let digits := (s.drop 2).toString
    if digits.all Char.isDigit then digits.toNat? else none
  else none

/-- Is `s` a candidate for the loose-match (directive prefix)?
    The loose form catches near-misses so typos surface as TH9003 instead of
    being silently treated as a comment. -/
private def isLooseMatch (trimmed : String) : Bool :=
  trimmed.startsWith "@thales-expect-error" ||
  trimmed.startsWith "@thales-expect_error" ||
  trimmed.startsWith "@thales_expect-error" ||
  trimmed.startsWith "@thales_expect_error" ||
  trimmed.startsWith "@thales-expect-err" ||
  trimmed.startsWith "@thales-expect-errror" ||
  trimmed.startsWith "@thales-expect-erorr" ||
  trimmed.startsWith "@thales-expecterror"

/-- Parse the textual content of a `//` line comment (no `//` prefix).
    Returns how it classifies against the directive grammar. -/
def parseDirectiveContent (content : String) : DirectiveMatch :=
  let trimmed := ltrim content
  if !isLooseMatch trimmed then .notADirective
  else if !trimmed.startsWith "@thales-expect-error" then .malformed
  else
    let rest := (trimmed.drop "@thales-expect-error".length).toString
    let rest' := rtrim rest
    if rest'.isEmpty then .strict none
    else
      -- Must begin with at least one space/tab, then the TH code, then nothing.
      if !(isSpaceOrTab rest'.front) then .malformed
      else
        match parseTHCode (ltrim rest') with
        | some n => .strict (some n)
        | none => .malformed

end ExpectError

namespace JSDoc

/-- Is this character valid in a TS identifier? -/
private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '$'

/-- Is this character a valid TS identifier start? -/
private def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_' || c == '$'

/-- Strip leading ASCII whitespace (space/tab/newline/carriage-return). -/
private def ltrimWS (s : String) : String :=
  let rec go : List Char → List Char
    | [] => []
    | c :: cs => if c == ' ' || c == '\t' || c == '\n' || c == '\r' then go cs else c :: cs
  String.ofList (go s.toList)

/-- Parse `@throws T1 | T2 | ...` from the rest of the line after `@throws`.
    Returns the list of type names (may be empty if none found). -/
private def parseThrowsTypes (rest : String) : List String :=
  -- Split by '|' and trim each segment; keep non-empty identifier-like names
  let segments := rest.splitOn "|"
  segments.filterMap fun seg =>
    let trimmed := ltrimWS seg
    -- Take leading identifier chars
    let name := String.ofList (trimmed.toList.takeWhile isIdentChar)
    if name.isEmpty || !isIdentStart name.front then none
    else some name

/-- Append a list of types to an existing `ThrowsAnnotation`, transitioning
    `.absent` to `.declared` on first `@throws` line. -/
def appendThrows :
    Thales.AST.ThrowsAnnotation → List String → Thales.AST.ThrowsAnnotation
  | .absent,       ts => .declared ts
  | .declared old, ts => .declared (old ++ ts)

/-- Parse a JSDoc block body (contents after `/**` and before `*/`).
    Returns a `JSDocDirectives` with all `@throws` and `@total` data found. -/
def parseJSDocBlock (body : String) : JSDocDirectives :=
  -- Split into lines and look for @throws / @total in each
  let lines := body.splitOn "\n"
  let init : JSDocDirectives := {}
  lines.foldl (fun acc line =>
    -- Strip leading whitespace and any leading '*' (common JSDoc style)
    let stripped := ltrimWS line
    let stripped := if stripped.startsWith "*" then ltrimWS (stripped.drop 1 |>.toString) else stripped
    if stripped.startsWith "@throws" then
      let rest := (stripped.drop "@throws".length).toString
      let types := parseThrowsTypes rest
      { acc with throwsAnn := appendThrows acc.throwsAnn types }
    else if stripped.startsWith "@total" then
      -- Only treat as @total if followed by whitespace, end of line, or nothing
      let rest := (stripped.drop "@total".length).toString
      let valid := rest.isEmpty || rest.front == ' ' || rest.front == '\t'
      { acc with total := acc.total || valid }
    else acc) init

end JSDoc

end Thales.Parser
