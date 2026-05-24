/-
  Thales/TypeCheck/TSAST.lean
  TypeScript-augmented AST nodes wrapping the JS AST
-/
import Thales.AST
import Thales.TypeCheck.TSType
import Thales.Parser.ExpectError

namespace Thales.TypeCheck

open Thales.AST

/-- Enum member: Red, Green = 1, Blue = "blue" -/
structure TSEnumMember where
  name : String
  init : Option Expression := none
  deriving Inhabited

/-- Interface member (for interface declarations) -/
inductive TSInterfaceMember where
  | property (name : String) (type : TSType) (optional : Bool) (readonly : Bool)
  | method (name : String) (params : List TSParamType) (returnType : TSType) (optional : Bool)
  deriving Inhabited

/-- TS-augmented statement: either a plain JS statement or a TS-specific one -/
inductive TSStatement where
  | js (s : Statement)
  | annotatedVarDecl (base : NodeBase) (kind : VariableKind)
      (name : String) (typeAnn : Option TypeAnnotation) (init : Option Expression)
  | annotatedFuncDecl (base : NodeBase) (name : String)
      (typeParams : List TSTypeParam)
      (params : List (String × Option TypeAnnotation × Bool × Bool))
      (returnType : Option TypeAnnotation) (body : Statement)
      (generator : Bool := false) (async : Bool := false)
      (throwsAnn : ThrowsAnnotation := .absent)  -- @throws JSDoc directive
      (total : Bool := false)                    -- true iff @total directive present
  | interfaceDecl (base : NodeBase) (name : String)
      (typeParams : List TSTypeParam)
      (extends_ : List String) (members : List TSInterfaceMember)
  | typeAliasDecl (base : NodeBase) (name : String)
      (typeParams : List TSTypeParam) (type : TSType)
  | enumDecl (base : NodeBase) (name : String)
      (members : List TSEnumMember) (isConst : Bool)
  | declareStmt (base : NodeBase) (inner : TSStatement)
  /-- ES module import declaration: `import { Foo, Bar } from './geom';`
      `source` is the raw module specifier string (e.g. `"./geom"`).
      `specifiers` holds the local names (empty for side-effect imports). -/
  | importDecl (base : NodeBase) (source : String) (specifiers : List String)

instance : Inhabited TSStatement := ⟨.js (.emptyStmt {})⟩

/-- TS-augmented expression: either a plain JS expression or a TS-specific one -/
inductive TSExpression where
  | js (e : Expression)
  | asExpr (expr : TSExpression) (type : TSType)
  | satisfiesExpr (expr : TSExpression) (type : TSType)
  | nonNullAssert (expr : TSExpression)

instance : Inhabited TSExpression := ⟨.js (.literal {} (.null) "null")⟩

/-- Source location of a TS-augmented expression. TS-only wrappers
    (`as`, `satisfies`, `!`) delegate to the inner expression. -/
def tsExprLoc : TSExpression → Option SourceLocation
  | .js e             => exprLoc e
  | .asExpr inner _
  | .satisfiesExpr inner _
  | .nonNullAssert inner => tsExprLoc inner

/-- A TS program is a list of TS statements -/
structure TSProgram where
  base : NodeBase := {}
  body : List TSStatement
  sourceType : String := "script"
  /-- `@thales-expect-error` directives collected by the lexer.
      Empty for programs produced by paths that do not track directives. -/
  expectErrorDirectives : Array Thales.Parser.ExpectErrorDirective := #[]
  deriving Inhabited

end Thales.TypeCheck
