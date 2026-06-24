/-
  Thales/TypeCheck/ModuleExports.lean
  Pure collector of a module's publicly-exported signatures.

  Used by the IO resolver in `Main.lean`: when the entry imports `./a`, the
  resolver parses `a.ts`, calls `collectModuleExports`, and seeds the entry's
  `TypeContext` with the imported (aliased) bindings and all exported types. Only
  signatures are harvested — bodies are never re-checked here (each file is
  type-checked independently by its own `thales` invocation). This mirrors how
  `tsc -b` consumes a dependency's `.d.ts` rather than its source.
-/
import Thales.TypeCheck.TSAST
import Thales.TypeCheck.TSType
import Thales.TypeCheck.Context

namespace Thales.TypeCheck

/-- The publicly-exported surface of one module. -/
structure ModuleExports where
  values : List (String × TSType) := []          -- exported value bindings (public name → type)
  aliases : List (String × TypeAliasDef) := []    -- exported type aliases
  interfaces : List (String × InterfaceDef) := [] -- exported interfaces
  deriving Inhabited

/-- Build the value type of a function declaration from its annotations (no body check). -/
private def funcSig (params : List (String × Option TypeAnnotation × Bool × Bool))
    (returnType : Option TypeAnnotation) : TSType :=
  let ps := params.map fun (pname, ann, opt, rest_) =>
    TSParamType.mk pname (ann.elim .any (·.type)) opt rest_
  TSType.function ps (returnType.elim .any (·.type))

/-- Collect a declaration's exported surface contribution (the inner of `export <decl>`). -/
private def exportOne (s : TSStatement) : ModuleExports :=
  match s with
  | .annotatedFuncDecl _ name _tps params ret _ _ _ _ _ =>
      { values := [(name, funcSig params ret)] }
  | .annotatedVarDecl _ _ name (some ann) _ => { values := [(name, ann.type)] }
  | .annotatedVarDecl _ _ name none (some _) => { values := [(name, .any)] }  -- v1: unannotated export → any
  | .interfaceDecl _ name tps _ members => { interfaces := [(name, { typeParams := tps, members })] }
  | .typeAliasDecl _ name tps ty => { aliases := [(name, { typeParams := tps, body := ty })] }
  | _ => {}

private def merge (a b : ModuleExports) : ModuleExports :=
  { values := a.values ++ b.values
    aliases := a.aliases ++ b.aliases
    interfaces := a.interfaces ++ b.interfaces }

/-- A local-name → public-name table for trailing `export { local as public }`.
    `sp.imported` is the local declared name; `sp.localName` is the exported name. -/
private def renameTable (specs : List ModuleSpecifier) : List (String × String) :=
  specs.map fun sp => (sp.imported, sp.localName)

/-- Collect the full exported surface of a parsed module. -/
def collectModuleExports (prog : TSProgram) : ModuleExports := Id.run do
  -- 1) inline exports
  let mut acc : ModuleExports := {}
  for s in prog.body do
    match s with
    | .exportDecl _ inner => acc := merge acc (exportOne inner)
    | _ => pure ()
  -- 2) trailing `export { … }` over already-declared top-level names
  let renames := prog.body.foldl (fun r s => match s with
    | .exportNamedDecl _ specs => r ++ renameTable specs
    | _ => r) []
  if renames.isEmpty then return acc
  -- `declared` intentionally indexes ALL top-level decls so a trailing
  -- `export { g }` can find a `g` that was declared without inline `export`.
  let declared := prog.body.foldl (fun (m : ModuleExports) s => merge m (exportOne s)) {}
  for (localName, publicName) in renames do
    match declared.values.find? (·.1 == localName) with
    | some (_, ty) => acc := merge acc { values := [(publicName, ty)] }
    | none =>
      match declared.interfaces.find? (·.1 == localName) with
      | some (_, idef) => acc := merge acc { interfaces := [(publicName, idef)] }
      | none => match declared.aliases.find? (·.1 == localName) with
        | some (_, adef) => acc := merge acc { aliases := [(publicName, adef)] }
        | none => pure ()
  return acc

end Thales.TypeCheck
