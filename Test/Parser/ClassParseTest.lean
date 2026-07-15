import Thales.Parser.Native

/-!
Parser retention test for class member information (#106): the parser must
keep `readonly`/accessibility modifiers, field type annotations, method
signatures (params + return type), and class-level `abstract`/generic/
`implements` flags instead of discarding them.

The Pratt parser is built from `partial def`s, so it does not reduce under
`#guard`; assertions run via `#eval` (executed at `lake build ThalesTest`),
throwing on mismatch.
-/

namespace Thales.Parser.ClassParse.Test

open Thales Thales.AST Thales.TypeCheck

private def src : String :=
  "interface I { x: bigint }\n" ++
  "class Point implements I {\n" ++
  "  readonly x: bigint;\n" ++
  "  mut: bigint;\n" ++
  "  private secret: bigint;\n" ++
  "  constructor(x: bigint, mut: bigint) { this.x = x; this.mut = mut; this.secret = 0n; }\n" ++
  "  norm1(): bigint { return this.x; }\n" ++
  "  translate(dx: bigint, dy: bigint): Point { return this; }\n" ++
  "}\n" ++
  "abstract class A {}\n"

private def keyName : Expression → String
  | .identifier _ n => n
  | _ => "<non-identifier>"

private def findField (els : List ClassElement) (name : String) : Option FieldDefinition :=
  els.findSome? fun el => match el with
    | .field (fd@(.mk _ key ..)) => if keyName key == name then some fd else none
    | _ => none

private def findMethod (els : List ClassElement) (name : String) : Option MethodDefinition :=
  els.findSome? fun el => match el with
    | .method (md@(.mk _ key ..)) => if keyName key == name then some md else none
    | _ => none

private def classDecls (prog : TSProgram) : List Statement :=
  prog.body.filterMap fun s => match s with
    | .js (stmt@(.classDecl ..)) => some stmt
    | _ => none

#eval show IO Unit from do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse failed: {e}")
  | .ok prog =>
    match classDecls prog with
    | [point, a] =>
      -- Class-level flags on Point
      match point with
      | .classDecl _ id superClass els isAbstract hasTypeParams hasImplements =>
        unless id.name == "Point" do throw (IO.userError s!"class name: {id.name}")
        unless superClass.isNone do throw (IO.userError "Point should have no superclass")
        unless isAbstract == false do throw (IO.userError "Point marked abstract")
        unless hasTypeParams == false do throw (IO.userError "Point marked generic")
        unless hasImplements == true do throw (IO.userError "Point implements flag not set")
        -- field x: readonly, annotated bigint, not optional, no accessibility
        match findField els "x" with
        | some (.mk _ _ _ _ _ _ readonly optional typeAnnotation accessibility) =>
          unless readonly == true do throw (IO.userError "x not readonly")
          unless optional == false do throw (IO.userError "x marked optional")
          unless typeAnnotation == some TSType.bigint do
            throw (IO.userError "x annotation is not bigint")
          unless accessibility.isNone do throw (IO.userError "x has accessibility")
        | none => throw (IO.userError "field x not found")
        -- field mut: not readonly
        match findField els "mut" with
        | some (.mk _ _ _ _ _ _ readonly _ _ _) =>
          unless readonly == false do throw (IO.userError "mut marked readonly")
        | none => throw (IO.userError "field mut not found")
        -- field secret: private accessibility
        match findField els "secret" with
        | some (.mk _ _ _ _ _ _ _ _ _ accessibility) =>
          unless accessibility == some Accessibility.private_ do
            throw (IO.userError "secret is not private")
        | none => throw (IO.userError "field secret not found")
        -- constructor: kind, two annotated sigParams
        match findMethod els "constructor" with
        | some (.mk _ _ _ kind _ _ _ _ _ _ _ sigParams _) =>
          unless kind == MethodKind.constructor do throw (IO.userError "ctor kind wrong")
          match sigParams with
          | [(n1, some ann1, false, false), (n2, some ann2, false, false)] =>
            unless n1 == "x" && n2 == "mut" do
              throw (IO.userError s!"ctor param names: {n1}, {n2}")
            unless ann1.type == TSType.bigint && ann2.type == TSType.bigint do
              throw (IO.userError "ctor param annotations are not bigint")
          | _ => throw (IO.userError s!"ctor sigParams shape wrong ({sigParams.length} params)")
        | none => throw (IO.userError "constructor not found")
        -- norm1: no params, annotated return
        match findMethod els "norm1" with
        | some (.mk _ _ _ _ _ _ _ _ _ _ _ sigParams returnType) =>
          unless sigParams.isEmpty do throw (IO.userError "norm1 should have no params")
          unless (returnType.map (·.type)) == some TSType.bigint do
            throw (IO.userError "norm1 return type is not bigint")
        | none => throw (IO.userError "method norm1 not found")
        -- translate: two annotated sigParams
        match findMethod els "translate" with
        | some (.mk _ _ _ _ _ _ _ _ _ _ _ sigParams _) =>
          match sigParams with
          | [(_, some _, _, _), (_, some _, _, _)] => pure ()
          | _ => throw (IO.userError "translate sigParams not two annotated entries")
        | none => throw (IO.userError "method translate not found")
      | _ => throw (IO.userError "first class is not a classDecl")
      -- abstract class A {}
      match a with
      | .classDecl _ id _ _ isAbstract _ _ =>
        unless id.name == "A" do throw (IO.userError s!"second class name: {id.name}")
        unless isAbstract == true do throw (IO.userError "A not marked abstract")
      | _ => throw (IO.userError "second class is not a classDecl")
      IO.println "ClassParseTest: OK"
    | other =>
      throw (IO.userError s!"expected 2 class decls, got {other.length}")

end Thales.Parser.ClassParse.Test
