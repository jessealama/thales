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
  classes : List (String × ClassInfo) := []       -- exported classes (instance type + ctor signature)
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
  | .js (stmt@(.classDecl _ id ..)) =>
      match classInfoOfDecl stmt with
      | some info => { classes := [(id.name, info)] }
      | none => {}
  | _ => {}

private def merge (a b : ModuleExports) : ModuleExports :=
  { values := a.values ++ b.values
    aliases := a.aliases ++ b.aliases
    interfaces := a.interfaces ++ b.interfaces
    classes := a.classes ++ b.classes }

namespace ModuleExports

/-- Re-export the member named `localName` under `publicName`, searching values,
    then interfaces, then aliases. Empty when `localName` isn't declared. -/
def reexportAs (m : ModuleExports) (localName publicName : String) : ModuleExports :=
  match m.values.find? (·.1 == localName) with
  | some (_, ty) => { values := [(publicName, ty)] }
  | none => match m.classes.find? (·.1 == localName) with
    | some (_, cinfo) => { classes := [(publicName, cinfo)] }
    | none => match m.interfaces.find? (·.1 == localName) with
      | some (_, idef) => { interfaces := [(publicName, idef)] }
      | none => match m.aliases.find? (·.1 == localName) with
        | some (_, adef) => { aliases := [(publicName, adef)] }
        | none => {}

/-- Is `name` part of this module's exported surface (value, class, interface, or alias)? -/
def member? (m : ModuleExports) (name : String) : Bool :=
  m.values.any (·.1 == name) || m.classes.any (·.1 == name)
    || m.interfaces.any (·.1 == name) || m.aliases.any (·.1 == name)

/-- Seed `ctx` with this module's exported surface for an importer: bind each
    explicitly-imported value (and type) name under its local alias, and merge ALL
    exported types so imported signatures that reference them resolve. Names not
    exported are left unbound — the import site raises TS2305 for them. -/
def seedContext (exp : ModuleExports) (ctx : TypeContext)
    (imp : List ModuleSpecifier) : TypeContext := Id.run do
  let mut c := ctx
  -- merge ALL exported types so imported signatures referencing them resolve
  for (n, idef) in exp.interfaces do c := { c with interfaces := c.interfaces.insert n idef }
  for (n, adef) in exp.aliases do c := { c with typeAliases := c.typeAliases.insert n adef }
  for (n, cinfo) in exp.classes do c := { c with classes := c.classes.insert n cinfo }
  -- bind each imported name (value or type) under its local alias
  for sp in imp do
    match exp.values.find? (·.1 == sp.imported) with
    | some (_, ty) => c := { c with bindings := c.bindings.insert sp.localName ty }
    | none => pure ()
    match exp.classes.find? (·.1 == sp.imported) with
    | some (_, cinfo) =>
      -- mirror `withClass`: register the class and bind its name as a value
      c := { c with
        classes := c.classes.insert sp.localName cinfo
        bindings := c.bindings.insert sp.localName (.ref sp.localName []) }
    | none => pure ()
    match exp.interfaces.find? (·.1 == sp.imported) with
    | some (_, idef) => c := { c with interfaces := c.interfaces.insert sp.localName idef }
    | none => match exp.aliases.find? (·.1 == sp.imported) with
      | some (_, adef) => c := { c with typeAliases := c.typeAliases.insert sp.localName adef }
      | none => pure ()
  return c

end ModuleExports

/-- Collect the full exported surface of a parsed module. -/
def collectModuleExports (prog : TSProgram) : ModuleExports := Id.run do
  -- 1) inline exports
  let mut acc : ModuleExports := {}
  for s in prog.body do
    match s with
    | .exportDecl _ inner => acc := merge acc (exportOne inner)
    | _ => pure ()
  -- 2) trailing `export { local as public }` over already-declared top-level
  -- names. `declared` intentionally indexes ALL top-level decls so a trailing
  -- `export { g }` can find a `g` that was declared without inline `export`.
  let declared := prog.body.foldl (fun (m : ModuleExports) s => merge m (exportOne s)) {}
  for s in prog.body do
    match s with
    | .exportNamedDecl _ specs =>
      for sp in specs do acc := merge acc (declared.reexportAs sp.imported sp.localName)
    | _ => pure ()
  return acc

end Thales.TypeCheck
