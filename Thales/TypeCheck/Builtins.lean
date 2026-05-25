/-
  Thales/TypeCheck/Builtins.lean
  Hardcoded built-in type table
  Replace with lib.d.ts parsing in a future phase.
-/
import Thales.TypeCheck.TSType
import Thales.TypeCheck.Context

namespace Thales.TypeCheck

/-- Helper: create a function type with named params -/
private def fnType (params : List (String × TSType)) (ret : TSType) : TSType :=
  .function (params.map fun (name, ty) => .mk name ty) ret

/-- Helper: create a function type with named params, some possibly optional -/
private def fnTypeOpt (params : List (String × TSType × Bool)) (ret : TSType) : TSType :=
  .function (params.map fun (name, ty, opt) => .mk name ty opt) ret

/-- Helper: create a rest-param function type -/
private def restFnType (restName : String) (restElem : TSType) (ret : TSType) : TSType :=
  .function [.mk restName (.array restElem) false true] ret

/-- Built-in variable bindings -/
def builtinBindings : List (String × TSType) :=
  let voidFn := restFnType "args" .any .void_
  let numToNum := fnType [("x", .number)] .number
  [
    -- console object
    ("console", .object [
      .property "log" voidFn false false,
      .property "error" voidFn false false,
      .property "warn" voidFn false false,
      .property "info" voidFn false false
    ]),
    -- Math object
    ("Math", .object [
      .property "floor" numToNum false false,
      .property "ceil" numToNum false false,
      .property "round" numToNum false false,
      .property "abs" numToNum false false,
      .property "sqrt" numToNum false false,
      .property "max" (restFnType "values" .number .number) false false,
      .property "min" (restFnType "values" .number .number) false false,
      .property "random" (fnType [] .number) false false,
      .property "PI" .number false true,
      .property "E" .number false true
    ]),
    -- Global functions
    ("parseInt", fnType [("s", .string)] .number),
    ("parseFloat", fnType [("s", .string)] .number),
    ("isNaN", fnType [("n", .any)] .boolean),
    ("isFinite", fnType [("n", .any)] .boolean),
    -- Number static methods
    ("Number", .object [
      .property "isNaN" (fnType [("n", .any)] .boolean) false false,
      .property "isFinite" (fnType [("n", .any)] .boolean) false false,
      .property "isSafeInteger" (fnType [("n", .any)] .boolean) false false,
      .property "parseInt" (fnType [("s", .string)] .number) false false,
      .property "parseFloat" (fnType [("s", .string)] .number) false false
    ]),
    -- Array static methods
    ("Array", .object [
      .property "isArray" (fnType [("x", .any)] .boolean) false false
    ]),
    -- String static methods
    ("String", .object [
      .property "fromCharCode" (restFnType "codes" .number .string) false false
    ]),
    -- JSON object
    ("JSON", .object [
      .property "stringify" (fnType [("value", .any)] .string) false false,
      .property "parse" (fnType [("text", .string)] .any) false false
    ]),
    -- undefined and NaN
    -- Object constructor/class
    ("Object", .object [
      .property "keys" (fnType [("o", .any)] (.array .string)) false false,
      .property "values" (fnType [("o", .any)] (.array .any)) false false,
      .property "entries" (fnType [("o", .any)] (.array (.tuple [.string, .any]))) false false,
      .property "assign" (fnType [("target", .any), ("source", .any)] .any) false false,
      .property "freeze" (fnType [("o", .any)] .any) false false,
      .property "create" (fnType [("o", .any)] .any) false false
    ]),
    -- undefined and NaN
    ("undefined", .undefined),
    ("NaN", .number),
    ("Infinity", .number)
  ]

/-- The element type of an array-like type. `.array T` returns `T`;
    tuples return the union of their element types; `.ref "Array" [T]`
    returns `T`; everything else returns `.any` (only used as a fallback
    for property lookup, which won't see those cases). -/
private def arrayElementType (ty : TSType) : TSType :=
  match ty with
  | .array elem => elem
  | .ref "Array" [elem] => elem
  | .tuple [] => .any
  | .tuple [single] => single
  | .tuple es => .union es
  | _ => .any

/-- Look up a property on a built-in primitive type -/
def builtinProperty (ty : TSType) (name : String) : Option TSType :=
  match ty with
  | .string | .stringLit _ => stringProperty name
  | .number | .numberLit _ => numberProperty name
  | .boolean | .booleanLit _ => booleanProperty name
  | .refinement _ => numberProperty name
  | .array _ | .ref "Array" _ => arrayProperty (arrayElementType ty) name
  | .tuple _ => arrayProperty (arrayElementType ty) name
  | _ => none
where
  stringProperty (name : String) : Option TSType :=
    match name with
    -- `string.length` is non-negative (and at most 2^53-1 on JS strings),
    -- so we expose it as `Natural` to enable bounds-aware indexing.
    | "length" => some (.refinement .natural)
    | "charAt" => some (fnType [("pos", .number)] .string)
    | "charCodeAt" => some (fnType [("index", .number)] .number)
    | "indexOf" => some (fnType [("searchString", .string)] .number)
    | "lastIndexOf" => some (fnType [("searchString", .string)] .number)
    | "includes" => some (fnType [("searchString", .string)] .boolean)
    | "startsWith" => some (fnType [("searchString", .string)] .boolean)
    | "endsWith" => some (fnType [("searchString", .string)] .boolean)
    | "slice" => some (fnTypeOpt [("start", .number, false), ("end", .number, true)] .string)
    | "substring" => some (fnTypeOpt [("start", .number, false), ("end", .number, true)] .string)
    | "toLowerCase" => some (fnType [] .string)
    | "toUpperCase" => some (fnType [] .string)
    | "trim" => some (fnType [] .string)
    | "trimStart" => some (fnType [] .string)
    | "trimEnd" => some (fnType [] .string)
    | "split" => some (fnType [("separator", .string)] (.array .string))
    | "replace" => some (fnType [("searchValue", .string), ("replaceValue", .string)] .string)
    | "replaceAll" => some (fnType [("searchValue", .string), ("replaceValue", .string)] .string)
    | "repeat" => some (fnType [("count", .number)] .string)
    | "padStart" => some (fnType [("maxLength", .number)] .string)
    | "padEnd" => some (fnType [("maxLength", .number)] .string)
    | "match" => some (fnType [("regexp", .any)] .any)
    | "search" => some (fnType [("regexp", .any)] .number)
    | "concat" => some (restFnType "strings" .string .string)
    | "at" => some (fnType [("index", .number)] (.union [.string, .undefined]))
    | "toString" => some (fnType [] .string)
    | "valueOf" => some (fnType [] .string)
    | _ => none
  numberProperty (name : String) : Option TSType :=
    match name with
    | "toFixed" => some (fnTypeOpt [("fractionDigits", .number, true)] .string)
    | "toPrecision" => some (fnTypeOpt [("precision", .number, true)] .string)
    | "toExponential" => some (fnTypeOpt [("fractionDigits", .number, true)] .string)
    | "toString" => some (fnType [] .string)
    | "valueOf" => some (fnType [] .number)
    | _ => none
  booleanProperty (name : String) : Option TSType :=
    match name with
    | "toString" => some (fnType [] .string)
    | "valueOf" => some (fnType [] .boolean)
    | _ => none
  arrayProperty (elem : TSType) (name : String) : Option TSType :=
    match name with
    -- `Array<T>.length` and tuple `length` are non-negative; we expose them
    -- as `Natural` so `i < xs.length` participates in the bounds analyzer
    -- (see Tasks 3.6 and 3.10).
    | "length" => some (.refinement .natural)
    -- v0.6 forEach/map/filter/reduce surface signatures. The callback's
    -- index parameter (`i`) is exposed as `Natural` so that future P3
    -- per-array-bound threading can lift `xs[i]` from `T | undefined`
    -- to `T` (deferred past v0.7 — see docs/subset.md "P3 deferral"
    -- and ADR-0002; v0.7 is a 0.6-completeness release).
    -- The element parameter is the array's element type.
    | "forEach" =>
      some (fnType
        [("callback", .function
          [.mk "value" elem false false,
           .mk "index" (.refinement .natural) false false]
          .void_)]
        .void_)
    | "map" =>
      -- The TS-side return type is `Array<U>` where U is inferred from
      -- the callback's return; v0.6 does not perform that inference, so
      -- we use `Array<any>` as a conservative placeholder. Callers using
      -- `.map` will still type-check without P3 lift.
      some (fnType
        [("callback", .function
          [.mk "value" elem false false,
           .mk "index" (.refinement .natural) false false]
          .any)]
        (.array .any))
    | "filter" =>
      some (fnType
        [("predicate", .function
          [.mk "value" elem false false,
           .mk "index" (.refinement .natural) false false]
          .boolean)]
        (.array elem))
    | "reduce" =>
      -- Like `map`, accumulator type stays `any` until v0.7's inference.
      some (fnType
        [("callback", .function
          [.mk "acc" .any false false,
           .mk "value" elem false false,
           .mk "index" (.refinement .natural) false false]
          .any),
         ("init", .any)]
        .any)
    | _ => none

/-- Create the initial type context with built-in bindings -/
def builtinContext : TypeContext :=
  { bindings := builtinBindings.foldl (fun m (k, v) => m.insert k v) {},
    classes := [("Object", .object [])].foldl (fun m (k, v) => m.insert k v) {} }

end Thales.TypeCheck
