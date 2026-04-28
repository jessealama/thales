/-
  Thales/TypeCheck/TypedExpression.lean
  Typed expression tree — every node carries its resolved TSType
-/
import Thales.TypeCheck.TSType
import Thales.TypeCheck.TSAST

namespace Thales.TypeCheck

open Thales.AST

/-- A typed expression: the original expression annotated with its resolved type.
    `children` stores typed subexpressions in left-to-right traversal order.
    Used for LSP hover/completion — find the narrowest TypedExpression
    whose source span contains the cursor. -/
structure TypedExpression where
  expr : TSExpression
  type : TSType
  children : Array TypedExpression
  deriving Inhabited

end Thales.TypeCheck
