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

/-- One named-import / named-export binding: `imported as localName`.
    For `import { a } …` both fields are `"a"`; for `import { a as b } …`
    `imported = "a"`, `localName = "b"`. -/
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

/-- Which unsupported ESM export form was written, carried by `exportUnsupported`
    so the subset checker can reject it precisely (TH0089). The in-subset forms —
    inline `export <decl>` and trailing `export { … }` — are their own
    `TSStatement` constructors (`exportDecl`/`exportNamedDecl`), not listed here. -/
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

/-- The executable top-level statements of a module, reconstructed as plain JS
    `Statement`s in source order: an `annotatedVarDecl` becomes a `let`/`const`
    `variableDecl` (so escape analysis sees the binding, not just later
    mutations of it), a `.js` statement is unwrapped, `export <decl>` is
    unwrapped first, and pure declarations (functions, types, interfaces, enums,
    imports) are dropped. Feeds module-level mutation/escape analysis the SAME
    block the emitter lowers into `def main`, so the subset checker and the
    emitter never disagree on what is lowerable (#49). -/
def moduleExecutableStatements (body : List TSStatement) : List Statement :=
  (body.map fun s => match s with | .exportDecl _ inner => inner | other => other).filterMap
    fun ts => match ts with
    | .js (.variableDecl _) => none  -- top-level var decls arrive as annotatedVarDecl
    | .js s => some s
    | .annotatedVarDecl b kind name typeAnn init =>
        some (.variableDecl (.mk b [.mk b (.identifier { name }) init (typeAnn.map (·.type))] kind))
    | _ => none

end Thales.TypeCheck
