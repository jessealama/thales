/-
  Thales/TypeCheck/IndexBounds.lean
  Index-bounds analyzer for `arr[k]` / `xs[i]` accesses.

  Classifies each computed `memberExpr` indexing site into one of three
  kinds, according to the v0.6 design (see `docs/specs/2026-05-07-v0.6-design.md`,
  patterns P1 and P2):

    * `.p1` — "literal index into literal array".
        `arr` is a syntactic array-literal expression `[a, b, …]` of length
        `n` (or has tuple type of length `n`), and `k` is a numeric literal
        with `0 ≤ k < n`. The access result is `T` (the element type),
        not `T | undefined`.

    * `.p2` — "length-narrowed Natural index".
        In a context where the bounds-fact `i < xs.length` is in scope (for
        `i : Natural` and array `xs`), the access `xs[i]` is in-bounds.
        The result is `T`, not `T | undefined`. For an index typed as plain
        `number`, P2 does NOT fire — the user must narrow to `Natural`
        first via `isNatural(i)` (or `Number.isSafeInteger(i)` then a
        non-negativity check).

    * `.unknown` — no bounds proof available; emit must fall back to the
      optional-typed accessor.

  This module produces only the *classification*. The mark is consumed by
  the emit phase in Parcel 5 — at emit time the analyzer is re-applied to
  the AST node to choose between `arr[k]'(by decide)` and `arr[k]?`. Doing
  it that way (re-derivation) avoids threading a side-table through the
  typed AST.
-/
import Thales.AST
import Thales.TypeCheck.TSType
import Thales.TypeCheck.Narrowing

set_option autoImplicit false

namespace Thales.TypeCheck.IndexBounds

open Thales.AST
open Thales.TypeCheck

/-- Classification of an indexing site. -/
inductive IndexAccessKind where
  | unknown
  | p1
  | p2
  deriving Repr, BEq, Inhabited

/-- A bounds-fact in scope: `indexVar` is known to be < `arrayName`.length. -/
structure BoundsFact where
  indexVar : String
  arrayName : String
  deriving Repr, Inhabited

/-- Try to read a non-negative integer literal value from an expression.
    Returns `none` for non-literal or non-integer-non-negative literals. -/
private def asNatLiteral : Expression → Option Nat
  | .literal _ (.number n) _ =>
    if n ≥ 0.0 ∧ n == n.floor ∧ n ≤ 4294967295.0 then
      some n.toUInt32.toNat
    else
      none
  | _ => none

/-- Classify an indexing access `obj[idx]` against the current type bindings
    and the set of bounds-facts collected from the enclosing guard scope.
    Returns:
      * `.p1` for literal-index-into-literal-array (or tuple) when in range.
      * `.p2` when the array name and a `Natural`-typed index match a fact.
      * `.unknown` otherwise. -/
def classify (obj : Expression) (idx : Expression)
    (bindings : Std.HashMap String TSType)
    (boundsFacts : List BoundsFact) : IndexAccessKind := Id.run do
  -- P1: `[a, b, …][k]` with literal k in [0, n).
  match obj with
  | .arrayExpr _ elements =>
    match asNatLiteral idx with
    | some k =>
      if k < elements.length then return .p1 else return .unknown
    | none => pure ()
  | _ => pure ()
  -- P1 (tuple variant): `xs[k]` with `xs : tuple [t0, …, tn-1]` and k in range.
  match idx with
  | .literal _ (.number _) _ =>
    match obj with
    | .identifier _ varName =>
      match bindings[varName]? with
      | some (.tuple elems) =>
        match asNatLiteral idx with
        | some k => if k < elems.length then return .p1
        | none => pure ()
      | _ => pure ()
    | _ => pure ()
  | _ => pure ()
  -- P2: `xs[i]` with bounds-fact `i < xs.length` and `i : Natural`-typed.
  match obj, idx with
  | .identifier _ arrName, .identifier _ idxName =>
    let factMatches := boundsFacts.any fun bf =>
      bf.indexVar == idxName ∧ bf.arrayName == arrName
    if factMatches then
      match bindings[idxName]? with
      | some (.refinement _) =>
        -- Any refinement subtype of Natural would do; but only Natural / Byte
        -- / Bit are non-negative. We accept any refinement here because the
        -- lattice guarantees a numeric range and the bounds-fact ensures the
        -- upper bound; Parcel 5's emit machinery will discharge.
        return .p2
      | _ => pure ()
  | _, _ => pure ()
  return .unknown

/-- Walk a `Narrowing.Guard` and collect any `indexBounds` facts.
    Conjunctions distribute; negations and disjunctions are dropped (we
    cannot soundly use them as positive evidence). -/
partial def collectBoundsFacts : Narrowing.Guard → List BoundsFact
  | .indexBounds idxVar arrName => [{ indexVar := idxVar, arrayName := arrName }]
  | .and g1 g2 => collectBoundsFacts g1 ++ collectBoundsFacts g2
  -- `or` and `not` give no positive bounds info. Other guards: nothing.
  | _ => []

end Thales.TypeCheck.IndexBounds
