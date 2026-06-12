/-
  Thales/Emit/LoopShape.lean
  Shared syntactic loop-shape classifier (#25). Single source of truth for
  EscapeAnalysis, SubsetCheck, and the emitter — gate predicates consulted
  by multiple phases must never disagree (the #40 lesson). Conditions that
  need binding types or the mutated set (array-typed RHS, loop-var
  reassignment, bound-ident mutation) are checked by callers that have that
  context; this module owns the purely syntactic shape.
-/
import Thales.AST

namespace Thales.Emit.LoopShape

open Thales.AST

/-- The for-of RHS forms whose element type the call sites can determine:
    a plain identifier (declared-type lookup) or an inline array literal. -/
inductive ForOfRhs where
  | ident (name : String)
  | arrayLit (rhs : Expression)

/-- Classification of a loop statement. -/
inductive LoopClass where
  /-- `for (const|let x of rhs)`, simple-ident head, no `await`. -/
  | forOf (varName : String) (rhs : ForOfRhs) (rhsExpr : Expression)
          (body : Statement)
  /-- `for (let i = 0; i < B; i++)`; bound is a non-negative integer
      literal (`.inl n`) or `arr.length` (`.inr arrName`). -/
  | canonicalFor (varName : String) (bound : Nat ⊕ String) (body : Statement)
  | notLowerable

/-- A non-negative integer-valued number literal, as a Nat. -/
private def asNatLiteral : Expression → Option Nat
  | .literal _ (.number n) _ =>
      if n.isFinite && n ≥ 0 && n == n.floor && n ≤ 4294967295.0 then
        some n.toUInt32.toNat
      else none
  | _ => none

def classifyLoop : Statement → LoopClass
  | .forOfStmt _ left right body await =>
      if await then .notLowerable
      else
        match left with
        | .inr (.mk _ [.mk _ (.identifier id) none _] kind) =>
            if kind == .var then .notLowerable
            else
              (match right with
               | .identifier _ n => .forOf id.name (.ident n) right body
               | .arrayExpr _ _  => .forOf id.name (.arrayLit right) right body
               | _ => .notLowerable)
        | _ => .notLowerable
  | .forStmt _ init test update body =>
      match init, test, update with
      | some (.inr (.mk _ [.mk _ (.identifier id) (some initE) _] kind)),
        some (.binaryExpr _ .lt (.identifier _ tv) boundE),
        some (.updateExpr _ .inc (.identifier _ uv) _) =>
          if kind != .let_ || tv != id.name || uv != id.name then .notLowerable
          else if asNatLiteral initE != some 0 then .notLowerable
          else
            (match asNatLiteral boundE with
             | some n => .canonicalFor id.name (.inl n) body
             | none =>
               match boundE with
               | .memberExpr _ (.identifier _ arrName)
                   (.identifier _ "length") false _ =>
                   .canonicalFor id.name (.inr arrName) body
               | _ => .notLowerable)
      | _, _, _ => .notLowerable
  | _ => .notLowerable

/-- The statement is a loop, possibly wrapped in (further) labels. Callers
    poison labels-on-loops wholesale: `emitBodyDo` has no labeledStmt
    lowering. -/
partial def isLoopStmt : Statement → Bool
  | .whileStmt _ _ _ | .doWhileStmt _ _ _ | .forStmt _ _ _ _ _
  | .forInStmt _ _ _ _ | .forOfStmt _ _ _ _ _ => true
  | .labeledStmt _ _ inner => isLoopStmt inner
  | _ => false

/-- Unlabeled break/continue check: any LABELED break/continue anywhere in
    the own body (stopping at nested functions) poisons loop lowering. -/
partial def hasLabeledBreakOrContinue : Statement → Bool
  | .breakStmt _ (some _) | .continueStmt _ (some _) => true
  | .blockStmt _ ss => ss.any hasLabeledBreakOrContinue
  | .ifStmt _ _ c a =>
      hasLabeledBreakOrContinue c
        || (match a with | some s => hasLabeledBreakOrContinue s | none => false)
  | .whileStmt _ _ b | .doWhileStmt _ b _ | .forStmt _ _ _ _ b
  | .forInStmt _ _ _ b | .forOfStmt _ _ _ b _
  | .labeledStmt _ _ b | .withStmt _ _ b => hasLabeledBreakOrContinue b
  | .switchStmt _ _ cases =>
      cases.any fun (.mk _ _ ss) => ss.any hasLabeledBreakOrContinue
  | .tryStmt _ b h f =>
      hasLabeledBreakOrContinue b
        || (match h with
            | some (.mk _ _ hb _) => hasLabeledBreakOrContinue hb
            | none => false)
        || (match f with | some s => hasLabeledBreakOrContinue s | none => false)
  | _ => false

/-- An unlabeled `continue` that binds to THIS loop: the walk descends
    through blocks/ifs/switch/try but stops at nested loops (whose own
    `continue` binds to them) and nested functions. TS `continue` in a
    do-while jumps to the test, but Lean's `repeat ... until` re-enters the
    body without checking — and in a while-desugared `for`, `continue`
    would skip the update clause — so those loop bodies stay rejected
    when this holds. -/
partial def hasOwnUnlabeledContinue : Statement → Bool
  | .continueStmt _ none => true
  | .blockStmt _ ss => ss.any hasOwnUnlabeledContinue
  | .ifStmt _ _ c a =>
      hasOwnUnlabeledContinue c
        || (match a with | some s => hasOwnUnlabeledContinue s | none => false)
  | .labeledStmt _ _ b | .withStmt _ _ b => hasOwnUnlabeledContinue b
  | .switchStmt _ _ cases =>
      cases.any fun (.mk _ _ ss) => ss.any hasOwnUnlabeledContinue
  | .tryStmt _ b h f =>
      hasOwnUnlabeledContinue b
        || (match h with
            | some (.mk _ _ hb _) => hasOwnUnlabeledContinue hb
            | none => false)
        || (match f with | some s => hasOwnUnlabeledContinue s | none => false)
  -- Nested loops and (nested-function-bearing) statements stop the walk.
  | _ => false

/-- A non-canonical C-style `for` that can desugar to
    `init; while (test) { body; update }`. Conditions:

    * NOT `canonicalFor`-shaped — the canonical form keeps its structural
      `for i in [0:B]` lowering (`@total`-friendly; a desugared `while` is
      not). A canonical SHAPE whose operand later fails the caller's array
      check stays rejected rather than falling back here, preserving the
      canonical-for operand boundaries.
    * init is empty, a bare expression, or a single-identifier `let`/`const`
      declarator WITH an initializer (`var` hoists; out of subset).
    * if an update clause exists, the body has no loop-level `continue` —
      TS `continue` runs the update, but the desugared `while` body would
      skip it. With no update clause, `continue` just re-checks the test
      in both, so it stays admitted.

    A missing test means `while (true)`. Labeled break/continue is the
    callers' (existing) poison check, as for the other loop shapes. -/
def generalForDesugarable : Statement → Bool
  | s@(.forStmt _ init _ update body) =>
      (match classifyLoop s with
       | .canonicalFor _ _ _ => false
       | .forOf _ _ _ _ => false
       | .notLowerable =>
        (match init with
         | none => true
         | some (.inl _) => true
         | some (.inr (.mk _ [.mk _ (.identifier _) (some _) _] kind)) =>
             kind != .var
         | some (.inr _) => false)
        && (update.isNone || !hasOwnUnlabeledContinue body))
  | _ => false

/-- The desugaring of a non-canonical `for`:
    `for (init; test; update) body` → `init; while (test) { body; update }`,
    with a missing test desugaring to `while (true)`. `none` unless
    `generalForDesugarable` holds and the body is free of labeled
    break/continue (no loop lowering supports labels). EscapeAnalysis,
    SubsetCheck, and the emitter all consume this one decomposition, so the
    phases cannot disagree about whether a `for` desugars or what it
    desugars to. The init binding outliving the loop in the enclosing block
    is safe: shadowing rejection (TH0032) keeps any same-named outer
    binding out, so no later read can resolve to the loop variable. -/
def desugarGeneralFor : Statement → Option (List Statement)
  | s@(.forStmt fb init test update body) =>
      if generalForDesugarable s && !hasLabeledBreakOrContinue body then
        let initStmts : List Statement := match init with
          | none => []
          | some (.inl e) => [.exprStmt fb e]
          | some (.inr vd) => [.variableDecl vd]
        let testE : Expression := match test with
          | some e => e
          | none => .literal fb (.boolean true) "true"
        let bodyStmts : List Statement :=
          (match body with
           | .blockStmt _ ss => ss
           | other => [other])
          ++ (match update with
              | some u => [.exprStmt fb u]
              | none => [])
        some (initStmts ++ [.whileStmt fb testE (.blockStmt fb bodyStmts)])
      else none
  | _ => none

end Thales.Emit.LoopShape
