/-
  Index-bounds analyzer for `arr[k]` / `xs[i]` accesses.

  Classifies each computed `memberExpr` indexing site so that emit can
  choose between an in-bounds accessor (`arr[k]'h`) and the optional
  fallback (`arr[k]?`):

    * `.byDecide` — literal index `k` into a literal array `[a, b, …]`
      or a tuple-typed binding, with `k` in range. The bound is
      decidable at compile time, so emit discharges with `by native_decide`.

    * `.byHypothesis` — `xs[i]` where `i` is refinement-typed (Natural
      or narrower) and a fact `i < xs.length` is in scope. Emit
      discharges with the corresponding `dite`-bound hypothesis.

    * `.unknown` — no bounds proof available; emit must fall back to
      the optional-typed accessor.
-/
import Thales.AST
import Thales.TypeCheck.TSType
import Std.Data.HashMap

set_option autoImplicit false

namespace Thales.TypeCheck.IndexBounds

open Thales.AST
open Thales.TypeCheck

/-- Classification of an indexing site. -/
inductive IndexAccessKind where
  | unknown
  | byDecide
  | byHypothesis
  deriving Repr, BEq, Inhabited

/-- A bounds-fact in scope: `indexVar` is known to be < `arrayName`.length. -/
structure BoundsFact where
  indexVar : String
  arrayName : String
  deriving Repr, Inhabited

/-- Try to read a non-negative integer literal value from an expression. -/
private def asNatLiteral : Expression → Option Nat
  | .literal _ (.number n) _ =>
    if n ≥ 0.0 ∧ n == n.floor ∧ n ≤ 4294967295.0 then
      some n.toUInt32.toNat
    else
      none
  | _ => none

/-- Classify an indexing access `obj[idx]` against the current type bindings
    and the set of bounds-facts collected from the enclosing guard scope. -/
def classify (obj : Expression) (idx : Expression)
    (bindings : Std.HashMap String TSType)
    (boundsFacts : List BoundsFact) : IndexAccessKind := Id.run do
  -- Literal index into a literal array `[a, b, …][k]`.
  match obj with
  | .arrayExpr _ elements =>
    match asNatLiteral idx with
    | some k =>
      if k < elements.length then return .byDecide else return .unknown
    | none => pure ()
  | _ => pure ()
  -- Literal index into a tuple-typed binding.
  match idx with
  | .literal _ (.number _) _ =>
    match obj with
    | .identifier _ varName =>
      match bindings[varName]? with
      | some (.tuple elems) =>
        match asNatLiteral idx with
        | some k => if k < elems.length then return .byDecide
        | none => pure ()
      | _ => pure ()
    | _ => pure ()
  | _ => pure ()
  -- Refinement-typed index with a matching `i < xs.length` fact.
  match obj, idx with
  | .identifier _ arrName, .identifier _ idxName =>
    let factMatches := boundsFacts.any fun bf =>
      bf.indexVar == idxName ∧ bf.arrayName == arrName
    if factMatches then
      match bindings[idxName]? with
      | some (.refinement _) => return .byHypothesis
      | _ => pure ()
  | _, _ => pure ()
  return .unknown

end Thales.TypeCheck.IndexBounds
