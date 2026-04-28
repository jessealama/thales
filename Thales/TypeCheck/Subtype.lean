/-
  Thales/TypeCheck/Subtype.lean
  Structural subtype relation for TypeScript types

  NOTE: isSubtype and checkAssignable are now defined in Generic.lean
  (in a mutual block with resolveTypeGeneric and evaluateConditionalType).
  This file re-exports them via the Generic import.
-/
import Thales.TypeCheck.TSType
import Thales.TypeCheck.Context
import Thales.TypeCheck.Generic

namespace Thales.TypeCheck

-- isSubtype and checkAssignable are defined in Generic.lean

end Thales.TypeCheck
