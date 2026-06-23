import Thales.Parser.Native

/-!
Parser round-trip for the ESM module forms widened in #18: a named import with
an `as` alias, an inline `export` on a declaration, a plain declaration, and a
trailing `export { … }`. Asserts the new `importDecl`/`exportDecl`/
`exportNamedDecl` shapes preserve specifiers, the import form, and aliases.

The Pratt parser is built from `partial def`s, so it does not reduce under
`#guard`; assertions run via `#eval` (executed at `lake build ThalesTest`),
throwing on mismatch.
-/

namespace Thales.Parser.ExportImportParse.Test

open Thales Thales.TypeCheck

private def src : String :=
  "import { makeFoo as build } from './a';\n" ++
  "export function f(): bigint { return 1n; }\n" ++
  "function g(): bigint { return 2n; }\n" ++
  "export { g };\n"

private def specPairs (specs : List ModuleSpecifier) : List (String × String) :=
  specs.map fun s => (s.imported, s.localName)

#eval show IO Unit from do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse failed: {e}")
  | .ok prog =>
    match prog.body with
    | [s0, s1, s2, s3] =>
      -- stmt 0: named import with alias `makeFoo as build`
      match s0 with
      | .importDecl _ source specs form typeOnly =>
        unless source == "./a" && form == .named && typeOnly == false
            && specPairs specs == [("makeFoo", "build")] do
          throw (IO.userError s!"stmt0 import mismatch: {source} {repr (specPairs specs)}")
      | _ => throw (IO.userError "stmt0 is not a named importDecl")
      -- stmt 1: inline export wrapping `function f`
      match s1 with
      | .exportDecl _ (.annotatedFuncDecl _ name ..) =>
        unless name == "f" do throw (IO.userError s!"stmt1 export name: {name}")
      | _ => throw (IO.userError "stmt1 is not exportDecl of a function")
      -- stmt 2: plain (unexported) `function g`
      match s2 with
      | .annotatedFuncDecl _ name .. =>
        unless name == "g" do throw (IO.userError s!"stmt2 func name: {name}")
      | _ => throw (IO.userError "stmt2 is not a plain annotatedFuncDecl")
      -- stmt 3: trailing `export { g }`
      match s3 with
      | .exportNamedDecl _ specs =>
        unless specPairs specs == [("g", "g")] do
          throw (IO.userError s!"stmt3 export specs: {repr (specPairs specs)}")
      | _ => throw (IO.userError "stmt3 is not exportNamedDecl")
      IO.println "ExportImportParseTest: OK"
    | other =>
      throw (IO.userError s!"expected 4 statements, got {other.length}")

end Thales.Parser.ExportImportParse.Test
