/-
  Test/Emit/ClassSubsetCheckTest.lean
  Per-member class validation (#106): TH0030 narrows to unsupported class
  *forms* (expressions/abstract/generic/implements); the v1 shape (readonly
  fields, assign-each-field-once ctor, public instance methods) passes; each
  unsupported member form draws its own TH0094-TH0102 code; general subset
  checks recurse into ctor/method bodies; hoisted class decls join TH0093.
-/
import Thales.Emit.SubsetCheck
import Thales.Parser.Native

open Thales.Emit
open Thales.Parser
open Thales.TypeCheck

/-- Helper: parse a TS source string, run subsetCheck, check for a code. -/
def expectCode (src : String) (code : Nat) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse error: {e}")
  | .ok prog =>
    let diags := subsetCheck prog
    unless diags.any (·.thalesCode? = some code) do
      let formatted := (diags.map (·.format "test.ts")).toList
      throw (IO.userError s!"expected TH{code}, got: {formatted}")

/-- Helper: assert that NO diagnostic with the given TH code fires. -/
def expectNoCode (src : String) (code : Nat) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse error: {e}")
  | .ok prog =>
    let diags := subsetCheck prog
    if diags.any (·.thalesCode? = some code) then
      let formatted := (diags.map (·.format "test.ts")).toList
      throw (IO.userError s!"expected no TH{code}, got: {formatted}")

/-- Assert no class-related code (TH0030/31/94..102) fires at all. -/
def expectNoClassCodes (src : String) : IO Unit := do
  for code in [30, 31, 94, 95, 96, 97, 98, 99, 100, 101, 102] do
    expectNoCode src code

private def pointClass : String :=
  "class Point {\n" ++
  "  readonly x: bigint;\n" ++
  "  readonly y: bigint;\n" ++
  "  constructor(x: bigint, y: bigint) { this.x = x; this.y = y; }\n" ++
  "  norm1(): bigint { return this.x < 0n ? -this.x : this.x; }\n" ++
  "  translate(dx: bigint, dy: bigint): Point { return new Point(this.x + dx, this.y + dy); }\n" ++
  "}\n"

-- Supported shape: no class diagnostics at all
def testSupportedShape : IO Unit := expectNoClassCodes
  (pointClass ++ "const p = new Point(3n, -4n);\nconst n = p.norm1();\n")

-- Self-recursion is allowed (not a forward reference)
def testSelfRecursionOk : IO Unit := expectNoCode
  "class C { f(n: bigint): bigint { return n <= 0n ? 0n : this.f(n - 1n); } }" 101

-- A method calling an EARLIER method is fine
def testBackwardRefOk : IO Unit := expectNoCode
  "class C { a(): bigint { return 1n; } b(): bigint { return this.a(); } }" 101

-- TH0030 forms
def testClassExpr : IO Unit := expectCode "const C = class { };" 30
def testAbstractClass : IO Unit := expectCode "abstract class A { }" 30
def testGenericClass : IO Unit := expectCode "class C<T> { }" 30
def testImplementsClause : IO Unit := expectCode
  "interface I { }\nclass C implements I { }" 30

-- TH0031 unchanged for extends (and member validation short-circuits)
def testExtends : IO Unit := expectCode "class B { }\nclass C extends B { }" 31

-- TH0094: accessors
def testGetter : IO Unit := expectCode
  "class C { get x(): bigint { return 1n; } }" 94
def testSetter : IO Unit := expectCode
  "class C { set x(v: bigint) { } }" 94

-- TH0095: statics
def testStaticMethod : IO Unit := expectCode
  "class C { static m(): bigint { return 1n; } }" 95
def testStaticBlock : IO Unit := expectCode
  "class C { static { } }" 95
def testStaticField : IO Unit := expectCode
  "class C { static x: bigint = 1n; }" 95

-- TH0096: private members
def testPrivateField : IO Unit := expectCode
  "class C { readonly x: bigint; private y: bigint; constructor(x: bigint, y: bigint) { this.x = x; this.y = y; } }" 96
def testHashPrivate : IO Unit := expectCode
  "class C { #x: bigint; constructor(x: bigint) { } }" 96
def testProtectedMethod : IO Unit := expectCode
  "class C { protected m(): bigint { return 1n; } }" 96

-- TH0097: field initializer (readonly + annotated + ctor-assigned, so 0097 fires alone)
def testFieldInitializer : IO Unit := do
  let src := "class C { readonly x: bigint = 1n; constructor(x: bigint) { this.x = x; } }"
  expectCode src 97
  for code in [30, 31, 94, 95, 96, 98, 99, 100, 101, 102] do
    expectNoCode src code

-- TH0098: field forms
def testNonReadonlyField : IO Unit := expectCode
  "class C { x: bigint; constructor(x: bigint) { this.x = x; } }" 98
def testOptionalField : IO Unit := expectCode
  "class C { readonly x?: bigint; constructor(x: bigint) { this.x = x; } }" 98
def testFieldMissingAnnotation : IO Unit := expectCode
  "class C { readonly x; constructor(x: bigint) { this.x = x; } }" 98
def testReservedFieldName : IO Unit := expectCode
  "class C { readonly mk: bigint; constructor(mk: bigint) { this.mk = mk; } }" 98

-- TH0099: ctor forms
def testCtorNonStraightLine : IO Unit := expectCode
  ("class C { readonly x: bigint; constructor(x: bigint) { " ++
   "if (x > 0n) { this.x = x; } else { this.x = -x; } } }") 99
def testCtorMissingAssignment : IO Unit := expectCode
  ("class C { readonly x: bigint; readonly y: bigint; " ++
   "constructor(x: bigint) { this.x = x; } }") 99
def testCtorDoubleAssignment : IO Unit := expectCode
  ("class C { readonly x: bigint; " ++
   "constructor(x: bigint) { this.x = x; this.x = x; } }") 99
def testCtorReadBeforeAssign : IO Unit := expectCode
  ("class C { readonly x: bigint; readonly y: bigint; " ++
   "constructor(x: bigint) { this.x = this.y; this.y = x; } }") 99
def testCtorReadAfterAssignOk : IO Unit := expectNoCode
  ("class C { readonly x: bigint; readonly y: bigint; " ++
   "constructor(x: bigint) { this.x = x; this.y = this.x + 1n; } }") 99
def testCtorDefaultParam : IO Unit := expectCode
  "class C { readonly x: bigint; constructor(x: bigint = 1n) { this.x = x; } }" 99
def testMissingCtorWithFields : IO Unit := expectCode
  "class C { readonly x: bigint; }" 99
def testTwoCtors : IO Unit := expectCode
  "class C { constructor(); constructor() { } }" 99
def testNoFieldsNoCtorOk : IO Unit := expectNoCode
  "class C { m(): bigint { return 1n; } }" 99

-- TH0100: method forms
def testAsyncMethod : IO Unit := expectCode
  "class C { async m(): bigint { return 1n; } }" 100
def testGeneratorMethod : IO Unit := expectCode
  "class C { *m(): bigint { return 1n; } }" 100
def testOptionalMethod : IO Unit := expectCode
  "class C { m?(): bigint; }" 100
def testGenericMethod : IO Unit := expectCode
  "class C { m<T>(x: T): T { return x; } }" 100
def testMethodMissingReturnType : IO Unit := expectCode
  "class C { m() { return 1n; } }" 100
def testOverrideMethod : IO Unit := expectCode
  "class C { override m(): bigint { return 1n; } }" 100
def testReservedMethodName : IO Unit := expectCode
  "class C { rec(): bigint { return 1n; } }" 100

-- TH0101: forward reference
def testForwardRef : IO Unit := expectCode
  "class C { a(): bigint { return this.b(); } b(): bigint { return 1n; } }" 101

-- TH0102: method used as a value
def testMethodAsValue : IO Unit := expectCode
  (pointClass ++ "const p = new Point(1n, 2n);\nconst f = p.norm1;\n") 102
def testMethodCallNotValue : IO Unit := expectNoCode
  (pointClass ++ "const p = new Point(1n, 2n);\nconst n = p.norm1();\n") 102

-- export interplay: supported export class is silent (in particular no TH0089);
-- validation recurses through the export wrapper
def testExportSupportedClass : IO Unit := do
  let src := "export " ++ pointClass
  expectNoClassCodes src
  expectNoCode src 89
def testExportClassWithGetter : IO Unit := expectCode
  "export class C { get x(): bigint { return 1n; } }" 94

-- General subset checks recurse into method and ctor bodies (TH0010: loops
-- are not admitted in class bodies)
def testLoopInMethodBody : IO Unit := expectCode
  "class C { m(): bigint { while (true) { } return 1n; } }" 10
def testLoopInCtorBody : IO Unit := expectCode
  ("class C { readonly x: bigint; " ++
   "constructor(x: bigint) { while (true) { } this.x = x; } }") 10

-- TH0093: a class lowers to hoisted defs, so a method reading a top-level
-- mutated `let` (a main-local binding) is rejected like a hoisted function
def testClassReadsTopLevelMutable : IO Unit := expectCode
  "let counter = 0n;\ncounter = 1n;\nclass C { m(): bigint { return counter; } }" 93

-- Switch exhaustiveness reaches into method bodies (TH0040): a
-- non-exhaustive switch on a discriminated union in a method is rejected;
-- an exhaustive one is admitted
private def shapeAlias : String :=
  "type Shape = { kind: 'c'; r: bigint } | { kind: 's'; s: bigint };\n"
def testNonExhaustiveSwitchInMethod : IO Unit := expectCode
  (shapeAlias ++
   "class M { pick(sh: Shape): bigint { switch (sh.kind) { case 'c': return sh.r; } return 0n; } }") 40
def testExhaustiveSwitchInMethodOk : IO Unit := do
  let src := shapeAlias ++
    "class M { pick(sh: Shape): bigint { switch (sh.kind) { case 'c': return sh.r; case 's': return sh.s; } } }"
  expectNoCode src 40
  expectNoCode src 41

-- A ctor referencing a same-class method — via `this` or another instance —
-- is a forward reference (ctor' is emitted before every method): TH0101
def testCtorCallsMethodViaInstance : IO Unit := expectCode
  ("class C { readonly x: bigint; constructor(o: C) { this.x = o.bump(); } " ++
   "bump(): bigint { return 1n; } }") 101

-- A ctor that constructs its own class would make `def ctor'` self-recursive
def testSelfRecursiveCtor : IO Unit := expectCode
  ("class R { readonly x: bigint; " ++
   "constructor(n: bigint) { this.x = n <= 0n ? 0n : new R(n - 1n).x + 1n; } }") 99

-- A ctor/method parameter named after the class shadows the return type
def testCtorParamShadowsClassName : IO Unit := expectCode
  "class Gate { readonly x: bigint; constructor(Gate: bigint) { this.x = Gate; } }" 99
def testMethodParamShadowsClassName : IO Unit := expectCode
  "class Gate { m(Gate: bigint): bigint { return Gate; } }" 100

-- Method params must be plain annotated identifiers (an optional param
-- would emit a partially-applied call): TH0100
def testOptionalMethodParam : IO Unit := expectCode
  "class C { m(y?: bigint): bigint { return 1n; } }" 100
def testRestMethodParam : IO Unit := expectCode
  "class C { m(...ys: bigint[]): bigint { return 0n; } }" 100

-- Overload signature + implementation parse as two same-named methods
def testOverloadSignatures : IO Unit := expectCode
  "class C { m(a: bigint): bigint; m(a: bigint): bigint { return a; } }" 100

-- Duplicate fields
def testDuplicateFields : IO Unit := expectCode
  ("class C { readonly x: bigint; readonly x: bigint; " ++
   "constructor(x: bigint) { this.x = x; } }") 98

-- Name-keyed checks (TH0004 mutating methods, the reduce→foldl emitter
-- special case) stay sound: those names are reserved for class methods
def testMutatorNameReserved : IO Unit := expectCode
  "class S { add(n: bigint): bigint { return n; } }" 100
def testReduceNameReserved : IO Unit := expectCode
  "class S { reduce(a: bigint, b: bigint): bigint { return a; } }" 100

#eval testSupportedShape
#eval testSelfRecursionOk
#eval testBackwardRefOk
#eval testClassExpr
#eval testAbstractClass
#eval testGenericClass
#eval testImplementsClause
#eval testExtends
#eval testGetter
#eval testSetter
#eval testStaticMethod
#eval testStaticBlock
#eval testStaticField
#eval testPrivateField
#eval testHashPrivate
#eval testProtectedMethod
#eval testFieldInitializer
#eval testNonReadonlyField
#eval testOptionalField
#eval testFieldMissingAnnotation
#eval testReservedFieldName
#eval testCtorNonStraightLine
#eval testCtorMissingAssignment
#eval testCtorDoubleAssignment
#eval testCtorReadBeforeAssign
#eval testCtorReadAfterAssignOk
#eval testCtorDefaultParam
#eval testMissingCtorWithFields
#eval testTwoCtors
#eval testNoFieldsNoCtorOk
#eval testAsyncMethod
#eval testGeneratorMethod
#eval testOptionalMethod
#eval testGenericMethod
#eval testMethodMissingReturnType
#eval testOverrideMethod
#eval testReservedMethodName
#eval testForwardRef
#eval testMethodAsValue
#eval testMethodCallNotValue
#eval testExportSupportedClass
#eval testExportClassWithGetter
#eval testLoopInMethodBody
#eval testLoopInCtorBody
#eval testClassReadsTopLevelMutable
#eval testNonExhaustiveSwitchInMethod
#eval testExhaustiveSwitchInMethodOk
#eval testCtorCallsMethodViaInstance
#eval testSelfRecursiveCtor
#eval testCtorParamShadowsClassName
#eval testMethodParamShadowsClassName
#eval testOptionalMethodParam
#eval testRestMethodParam
#eval testOverloadSignatures
#eval testDuplicateFields
#eval testMutatorNameReserved
#eval testReduceNameReserved
#eval IO.println "ClassSubsetCheckTest: OK"
