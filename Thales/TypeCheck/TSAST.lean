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

/-- One named-import / named-export binding: `imported as local`.
    For `import { a } …` both fields are `"a"`; for `import { a as b } …`
    `imported = "a"`, `local = "b"`. -/
structure ModuleSpecifier where
  imported : String
  localName : String
  deriving Repr, Inhabited

/-- Which ESM import form was written. Only `.named` is in-subset (v1);
    the others are parsed so the subset checker can reject them precisely. -/
inductive ImportForm where
  | named           -- import { a, b as c } from '…'
  | defaultImport   -- import D from '…'
  | namespaceImport -- import * as ns from '…'
  | sideEffect      -- import '…'
  deriving Repr, Inhabited, BEq

/-- Which ESM export form was written. `.inline` and `.named` are in-subset (v1). -/
inductive ExportForm where
  | defaultExport   -- export default …
  | reexport        -- export { … } from '…'  /  export * from '…'
  deriving Repr, Inhabited, BEq

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
  /-- ES module import. `source` is the raw specifier (e.g. `"./geom"`).
      `specs` are the named bindings (empty for side-effect / namespace).
      `form` records the written form; `typeOnly` is `import type { … }`. -/
  | importDecl (base : NodeBase) (source : String)
      (specs : List ModuleSpecifier) (form : ImportForm) (typeOnly : Bool)
  /-- Inline export on a declaration: `export function f …`, `export const …`,
      `export type …`, `export interface …`. Wraps the inner declaration. -/
  | exportDecl (base : NodeBase) (inner : TSStatement)
  /-- Trailing named export: `export { f, g as h };`. -/
  | exportNamedDecl (base : NodeBase) (specs : List ModuleSpecifier)
  /-- An unsupported export form, parsed only so the subset checker can reject it. -/
  | exportUnsupported (base : NodeBase) (form : ExportForm)

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
