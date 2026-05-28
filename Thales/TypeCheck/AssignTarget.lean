/-
  Thales/TypeCheck/AssignTarget.lean
  Classify the legality of an assignment / update target (LHS).
  Returns `some kind` if the LHS is not assignable, `none` otherwise.

  This module is parameterised over the type-synth function so it can be
  imported by `Synth.lean` (which provides `synthJSExpr`) without a cycle.
-/
import Thales.TypeCheck.Context
import Thales.TypeCheck.Diagnostic
import Thales.TypeCheck.TypedExpression
import Thales.TypeCheck.TSAST
import Thales.AST

namespace Thales.TypeCheck

open Thales.AST

/-- True if `propName` is a `readonly` property of an `InterfaceDef`. -/
private def interfaceHasReadonlyProp (def_ : InterfaceDef) (propName : String) : Bool :=
  def_.members.any fun
    | .property n _ _ readonly => n == propName && readonly
    | _ => false

/-- True if `propName` is a `readonly` property on every applicable face of `ty`.
    For unions, requires every face to mark the property readonly (matching tsc:
    a property writable via any union face is legally assignable on the union).
    Walks `.paren`, follows alias/enum/class refs via `resolveType`, and looks up
    interface refs in the `interfaces` map directly. -/
partial def isReadonlyMember (ty : TSType) (propName : String) : TypeCheckM Bool := do
  let resolved ← resolveType ty
  match resolved with
  | .object members =>
      pure <| members.any fun
        | .property n _ _ readonly => n == propName && readonly
        | _ => false
  | .union types =>
      let mut allReadonly := true
      for t in types do
        unless ← isReadonlyMember t propName do
          allReadonly := false
      pure allReadonly
  | .paren inner => isReadonlyMember inner propName
  | .ref name _ => do
      -- Interface references aren't resolved by `resolveType`; look them up here.
      let ctx ← read
      match ctx.interfaces[name]? with
      | some def_ => pure (interfaceHasReadonlyProp def_ propName)
      | none => pure false
  | _ => pure false

/-- Classify the LHS of an assignment / update expression.
    `synth` is the caller-provided expression synthesiser (typically
    `Synth.synthJSExpr`); passing it in this way avoids an import cycle. -/
def classifyAssignTarget
    (synth : Expression → TypeCheckM TypedExpression)
    : Expression → TypeCheckM (Option DiagnosticKind)
  | .identifier _ name => do
      if ← lookupConst name then
        pure (some (.cannotAssignToConstant name))
      else pure none
  | .memberExpr _ obj (.identifier _ propName) false _ => do
      let objTyped ← synth obj
      if ← isReadonlyMember objTyped.type propName then
        pure (some (.cannotAssignToReadOnlyProperty propName))
      else pure none
  | .memberExpr _ obj (.literal _ (.string s) _) true _ => do
      let objTyped ← synth obj
      if ← isReadonlyMember objTyped.type s then
        pure (some (.cannotAssignToReadOnlyProperty s))
      else pure none
  | .memberExpr _ _ _ true _ =>
      -- Bracket access with a non-string-literal key: we don't narrow that far.
      pure none
  | .memberExpr _ _ _ false _ =>
      -- Dot access with a non-identifier property — bail.
      pure none
  | _ =>
      -- Literal, call result, ternary, this, etc. — not an lvalue.
      pure (some .invalidAssignmentTarget)

end Thales.TypeCheck
