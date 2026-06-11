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

end Thales.Emit.LoopShape
