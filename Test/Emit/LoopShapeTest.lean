/-
  Test/Emit/LoopShapeTest.lean
  Pins the syntactic loop-shape classifier from Thales.Emit.LoopShape (#25).
  Each test parses a function whose body contains a single loop statement,
  digs it out, classifies it, and asserts the expected tag / fields.
-/
import Thales.Emit.LoopShape
import Thales.Parser.Native

open Thales.Emit.LoopShape
open Thales.Parser
open Thales.AST

/-- Parse `function f(xs: number[]): void { <body> }` and return the first
    statement in the function body. -/
private def firstStmt (src : String) : IO Statement := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse error: {e}")
  | .ok prog =>
    for ts in prog.body do
      if let .annotatedFuncDecl _ _ _ _ _ body _ _ _ _ := ts then
        match body with
        | .blockStmt _ (s :: _) => return s
        | _ => throw (IO.userError "function body is not a block or is empty")
    throw (IO.userError "no function decl found")

/-- Classify the first statement in `function f(xs: number[]): void { <loop> }`. -/
private def classifyFirst (loop : String) : IO LoopClass :=
  classifyLoop <$> firstStmt s!"function f(xs: number[]): void \{ {loop} }"

/-- Assert a loop is classified as `forOf`. -/
private def assertForOf (loop : String) : IO Unit := do
  let cls ← classifyFirst loop
  match cls with
  | .forOf _ _ _ _ => return
  | _ => throw (IO.userError s!"expected forOf, got notLowerable/canonicalFor for: {loop}")

/-- Assert a loop is classified as `canonicalFor`. -/
private def assertCanonicalFor (loop : String) : IO Unit := do
  let cls ← classifyFirst loop
  match cls with
  | .canonicalFor _ _ _ => return
  | _ => throw (IO.userError s!"expected canonicalFor for: {loop}")

/-- Assert a loop is classified as `notLowerable`. -/
private def assertNotLowerable (loop : String) : IO Unit := do
  let cls ← classifyFirst loop
  match cls with
  | .notLowerable => return
  | _ => throw (IO.userError s!"expected notLowerable for: {loop}")

-- ── for-of cases ──────────────────────────────────────────────────────────

-- `for (const x of xs)`: identifier RHS → forOf
def t_forOf_const : IO Unit := assertForOf "for (const x of xs) { }"

-- `for (let x of xs)`: let-declared var → forOf
def t_forOf_let : IO Unit := assertForOf "for (let x of xs) { }"

-- `for (const x of [1, 2])`: array literal RHS → forOf
def t_forOf_arrayLit : IO Unit := assertForOf "for (const x of [1, 2]) { }"

-- `for (const [a, b] of xs)`: destructuring head → notLowerable
def t_forOf_destructuring : IO Unit :=
  assertNotLowerable "for (const [a, b] of xs) { }"

-- `for (x of xs)`: expression head (no declaration) → notLowerable.
-- Use a separate parameter `x` so the parser accepts the for-of without a
-- variable declaration in the head (`left = .inl expression`).
def t_forOf_exprHead : IO Unit := do
  let cls ← classifyLoop <$>
    firstStmt "function f(x: number, xs: number[]): void { for (x of xs) { } }"
  match cls with
  | .notLowerable => return
  | _ => throw (IO.userError "expected notLowerable for expression-head for-of")

-- `for (const x of f())`: call-expression RHS → notLowerable
def t_forOf_callRhs : IO Unit :=
  assertNotLowerable "for (const x of f()) { }"

-- ── canonical C-style for cases ──────────────────────────────────────────

-- `for (let i = 0; i < 5; i++)`: literal bound → canonicalFor
def t_canonicalFor_litBound : IO Unit := assertCanonicalFor "for (let i = 0; i < 5; i++) { }"

-- `for (let i = 0; i < xs.length; i++)`: array-length bound → canonicalFor
def t_canonicalFor_lengthBound : IO Unit := assertCanonicalFor "for (let i = 0; i < xs.length; i++) { }"

-- `for (let i = 1; i < 5; i++)`: nonzero start → notLowerable
def t_canonicalFor_nonzeroStart : IO Unit :=
  assertNotLowerable "for (let i = 1; i < 5; i++) { }"

-- `for (let i = 0; i <= 5; i++)`: `<=` test → notLowerable
def t_canonicalFor_leq : IO Unit :=
  assertNotLowerable "for (let i = 0; i <= 5; i++) { }"

-- `for (let i = 0; i < 5; i += 2)`: step ≠ 1 → notLowerable
def t_canonicalFor_nonunitStep : IO Unit :=
  assertNotLowerable "for (let i = 0; i < 5; i += 2) { }"

-- `for (let i = 0; i < 5.5; i++)`: non-integer bound → notLowerable
def t_canonicalFor_floatBound : IO Unit :=
  assertNotLowerable "for (let i = 0; i < 5.5; i++) { }"

-- ── other loop shapes ──────────────────────────────────────────────────────

-- `while (true) {}` → notLowerable
def t_while : IO Unit := assertNotLowerable "while (true) { }"

-- `for (const k in xs) {}` → notLowerable (for-in, not for-of)
def t_forIn : IO Unit := assertNotLowerable "for (const k in xs) { }"

-- ── field extraction assertions ───────────────────────────────────────────

-- canonicalFor with literal bound must expose `.inl 5` and varName `"i"`
def t_canonicalFor_fields_lit : IO Unit := do
  let cls ← classifyFirst "for (let i = 0; i < 5; i++) { }"
  match cls with
  | .canonicalFor "i" (.inl 5) _ => return
  | .canonicalFor vn _ _ =>
      throw (IO.userError s!"wrong fields: varName={vn}, bound tag mismatch")
  | _ => throw (IO.userError "not canonicalFor")

-- canonicalFor with array-length bound must expose `.inr "xs"` and varName `"i"`
def t_canonicalFor_fields_length : IO Unit := do
  let cls ← classifyFirst "for (let i = 0; i < xs.length; i++) { }"
  match cls with
  | .canonicalFor "i" (.inr "xs") _ => return
  | .canonicalFor vn _ _ =>
      throw (IO.userError s!"wrong fields: varName={vn}, bound tag mismatch")
  | _ => throw (IO.userError "not canonicalFor")

-- ── hasLabeledBreakOrContinue ─────────────────────────────────────────────

-- positive: a labeled break inside a while body is detected
def t_labeledBreak_positive : IO Unit := do
  let s : Statement :=
    .whileStmt {} (.literal {} (.boolean true) "true")
      (.blockStmt {} [.breakStmt {} (some { name := "outer" })])
  unless hasLabeledBreakOrContinue s do
    throw (IO.userError "expected labeled break to be detected")

-- negative: an unlabeled break is not flagged
def t_labeledBreak_negative : IO Unit := do
  let s : Statement :=
    .whileStmt {} (.literal {} (.boolean true) "true")
      (.blockStmt {} [.breakStmt {} none])
  if hasLabeledBreakOrContinue s then
    throw (IO.userError "unlabeled break should not be flagged")

-- negative: a labeled break inside a nested function declaration is not flagged
-- (traversal stops at function boundaries via the catch-all)
def t_labeledBreak_nestedFunction : IO Unit := do
  let nestedBody : Statement :=
    .blockStmt {} [.breakStmt {} (some { name := "outer" })]
  let s : Statement :=
    .blockStmt {} [
      .functionDecl {} { name := "inner" } [] nestedBody false false
    ]
  if hasLabeledBreakOrContinue s then
    throw (IO.userError "labeled break inside nested function should not be flagged")

-- ── eval ──────────────────────────────────────────────────────────────────

#eval t_forOf_const
#eval t_forOf_let
#eval t_forOf_arrayLit
#eval t_forOf_destructuring
#eval t_forOf_exprHead
#eval t_forOf_callRhs
#eval t_canonicalFor_litBound
#eval t_canonicalFor_lengthBound
#eval t_canonicalFor_nonzeroStart
#eval t_canonicalFor_leq
#eval t_canonicalFor_nonunitStep
#eval t_canonicalFor_floatBound
#eval t_while
#eval t_forIn
#eval t_canonicalFor_fields_lit
#eval t_canonicalFor_fields_length
#eval t_labeledBreak_positive
#eval t_labeledBreak_negative
#eval t_labeledBreak_nestedFunction
