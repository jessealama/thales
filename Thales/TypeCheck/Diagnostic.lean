/-
  Thales/TypeCheck/Diagnostic.lean
  Type checker diagnostics with tsc error codes and TH#### Thales subset codes
-/
import Thales.TypeCheck.TSType
import Thales.AST

namespace Thales.TypeCheck

open Thales.AST

/-- Format a TSType for display in error messages -/
partial def formatType : TSType → String
  | .number => "number"
  | .string => "string"
  | .boolean => "boolean"
  | .bigint => "bigint"
  | .symbol => "symbol"
  | .void_ => "void"
  | .null_ => "null"
  | .undefined => "undefined"
  | .any => "any"
  | .never => "never"
  | .unknown => "unknown"
  | .refinement k => k.name
  | .numberLit n => toString n
  | .stringLit s => s!"\"{s}\""
  | .booleanLit true => "true"
  | .booleanLit false => "false"
  | .option inner => s!"{formatType inner} | null"
  | .array elem => s!"{formatType elem}[]"
  | .tuple elems =>
    let parts := elems.map formatType
    s!"[{String.intercalate ", " parts}]"
  | .function params ret =>
    let paramStrs := params.map fun (.mk name ty _ _) => s!"{name}: {formatType ty}"
    s!"({String.intercalate ", " paramStrs}) => {formatType ret}"
  | .union types =>
    let parts := types.map formatType
    String.intercalate " | " parts
  | .intersection types =>
    let parts := types.map formatType
    String.intercalate " & " parts
  | .object _ => "object"
  | .ref name _ => name
  | .typeVar _ name _ => name
  | .paren inner => formatType inner
  | .conditional check ext t f =>
    s!"{formatType check} extends {formatType ext} ? {formatType t} : {formatType f}"
  | .mapped k c v optMod roMod =>
    let ro := match roMod with | some true => "readonly " | some false => "-readonly " | none => ""
    let opt := match optMod with | some true => "?" | some false => "-?" | none => ""
    s!"\{ {ro}[{k} in {formatType c}]{opt}: {formatType v} }"

/-- Source of an `unannotatedThrow` diagnostic — used only to vary the
    user-facing message. Not part of the diagnostic's identity for
    `@thales-expect-error TH0060` matching. -/
inductive ThrowSource where
  | fromThrow
  | fromCall (callee : String)
  deriving Repr

/-- Thales subset violation kinds with TH#### codes -/
inductive ThalesKind where
  | cannotReassignVariable (name : String)
  | cannotAssignArrayElement
  | cannotAssignObjectProperty
  | cannotCallMutatingMethod (name : String)
  | cannotMutateCapturedVariable (name : String)
  | loopNotSupported
  | asyncNotSupported
  | anyNotPermitted
  | unknownNotPermitted
  | unionMustBeDiscriminated
  | intersectionNotSupported
  | typeLevelProgrammingNotSupported
  | nullUndefinedNotSupported
  | classNotSupported
  | inheritanceNotSupported
  | switchNotExhaustive (missingKinds : List String)
  | cannotVerifyTermination (funcName : String)
  -- @throws / @total diagnostics (TH0060–TH0070)
  -- TH0061 (unusedThrowsAnnotation), TH0062 (untypedCatch), TH0064
  -- (undeclaredPropagation) were removed in the strict-TS @throws redesign.
  -- TH0066 (header-level @total/@throws conflict) and TH0067 (body-level
  -- uncaught throw under @total) enforce that @total functions have no
  -- observable failure modes.
  | unannotatedThrow (source : ThrowSource)
  | nonRecordThrow
  | throwsRequiresTypeList
  | totalConflictsWithThrows
  | totalHasUncaughtThrow (source : ThrowSource)
  | totalityUnverified (leanError : String)
  -- Refinement-type diagnostics (TH0080–TH0081)
  | literalOutOfRange (literal : Float) (typeName : String) (min : Option Float) (max : Option Float)
  | refinementNeedsEvidence (sourceName : String) (targetTypeName : String)
  -- Directive diagnostics (TH9000–TH9003)
  | directiveUnused
  | directiveCodeMismatch (expected : Nat) (actual : List Nat)
  | emissionBlockedBySuppressedViolation
  | directiveMalformed
  -- Emit-soundness diagnostic (TH9004)
  | emittedCodeContainsSorry (filename : String)
  deriving Repr

/-- Map a ThalesKind to its numeric TH code -/
def ThalesKind.thCode : ThalesKind → Nat
  | .cannotReassignVariable _ => 1
  | .cannotAssignArrayElement => 2
  | .cannotAssignObjectProperty => 3
  | .cannotCallMutatingMethod _ => 4
  | .cannotMutateCapturedVariable _ => 5
  | .loopNotSupported => 10
  | .asyncNotSupported => 12
  | .anyNotPermitted => 20
  | .unknownNotPermitted => 21
  | .unionMustBeDiscriminated => 22
  | .intersectionNotSupported => 23
  | .typeLevelProgrammingNotSupported => 24
  | .nullUndefinedNotSupported => 25
  | .classNotSupported => 30
  | .inheritanceNotSupported => 31
  | .switchNotExhaustive _ => 40
  | .cannotVerifyTermination _ => 50
  | .unannotatedThrow _ => 60
  | .nonRecordThrow => 63
  | .throwsRequiresTypeList => 65
  | .totalConflictsWithThrows => 66
  | .totalHasUncaughtThrow _ => 67
  | .totalityUnverified _ => 70
  | .literalOutOfRange .. => 80
  | .refinementNeedsEvidence .. => 81
  | .directiveUnused => 9000
  | .directiveCodeMismatch .. => 9001
  | .emissionBlockedBySuppressedViolation => 9002
  | .directiveMalformed => 9003
  | .emittedCodeContainsSorry _ => 9004

/-- Zero-pad a numeric code to 4 digits -/
private def padCode (n : Nat) : String :=
  let s := toString n
  "".pushn '0' (4 - s.length) ++ s

/-- Human-readable message for each ThalesKind -/
def ThalesKind.message : ThalesKind → String
  | .cannotReassignVariable name => s!"Cannot reassign variable '{name}'"
  | .cannotAssignArrayElement => "Cannot assign to array element; use .concat or return a new array"
  | .cannotAssignObjectProperty => "Cannot assign to object property; construct a new object"
  | .cannotCallMutatingMethod name => s!"Cannot call mutating method '{name}'"
  | .cannotMutateCapturedVariable name => s!"Cannot mutate variable '{name}' captured by enclosing scope"
  | .loopNotSupported => "Loop not supported; use recursion or array methods"
  | .asyncNotSupported => "async/await not supported"
  | .anyNotPermitted => "'any' is not permitted"
  | .unknownNotPermitted => "'unknown' is not permitted in user code"
  | .unionMustBeDiscriminated => "Union must be discriminated (requires shared string-literal 'kind' field)"
  | .intersectionNotSupported => "Intersection types are not supported"
  | .typeLevelProgrammingNotSupported => "keyof/conditional/mapped types are not supported"
  | .nullUndefinedNotSupported => "null/undefined types are not supported; use Option<T>"
  | .classNotSupported => "'class' is not supported"
  | .inheritanceNotSupported => "Inheritance ('extends') is not supported"
  | .switchNotExhaustive missingKinds =>
    s!"Non-exhaustive switch on discriminated union (missing: {String.intercalate ", " missingKinds})"
  | .cannotVerifyTermination funcName =>
    s!"Cannot verify termination of '{funcName}'; add @decreasing hint or restructure"
  | .unannotatedThrow .fromThrow =>
    "Function body contains `throw` but no `@throws` annotation"
  | .unannotatedThrow (.fromCall callee) =>
    s!"Function calls `@throws`-annotated `{callee}` but is not itself annotated `@throws`"
  | .nonRecordThrow =>
    "Thrown value must be a record type"
  | .throwsRequiresTypeList =>
    "`@throws` must declare at least one error type (e.g. `@throws RangeError`)"
  | .totalConflictsWithThrows =>
    "`@total` and `@throws` cannot both be declared on the same function; remove one"
  | .totalHasUncaughtThrow .fromThrow =>
    "`@total` function has an uncaught `throw`; wrap it in `try`/`catch` or remove `@total`"
  | .totalHasUncaughtThrow (.fromCall callee) =>
    s!"`@total` function calls `@throws`-annotated `{callee}` outside `try`/`catch`; catch the failure or remove `@total`"
  | .totalityUnverified leanError =>
    s!"`@total` asserted but Lean could not prove termination: {leanError}"
  | .literalOutOfRange lit tyName min max =>
    let bound := match min, max with
      | some lo, some hi => s!" (must be in [{lo}, {hi}])"
      | some lo, none => s!" (min {lo})"
      | none, some hi => s!" (max {hi})"
      | none, none => ""
    s!"Literal {lit} out of range for {tyName}{bound}"
  | .refinementNeedsEvidence sourceName tyName =>
    s!"Value '{sourceName}' of type 'number' is not assignable to '{tyName}' without narrowing or constructor evidence"
  | .directiveUnused => "Unused `@thales-expect-error` directive"
  | .directiveCodeMismatch expected actual =>
    let fmtCode (n : Nat) : String := s!"TH{padCode n}"
    let actualStr := String.intercalate ", " (actual.map fmtCode)
    s!"`@thales-expect-error` expects {fmtCode expected} but got {actualStr}"
  | .emissionBlockedBySuppressedViolation =>
    "Cannot emit: file contains subset violations suppressed by `@thales-expect-error`"
  | .directiveMalformed =>
    "Malformed `@thales-expect-error` directive"
  | .emittedCodeContainsSorry filename =>
    s!"Emitted Lean code in '{filename}' contains 'sorry' or 'sorryAx'; emit must be sorry-free"

/-- Diagnostic error kinds with tsc error code mapping -/
inductive DiagnosticKind where
  | typeNotAssignable (source : TSType) (target : TSType)
  | argumentTypeMismatch (argIdx : Nat) (source : TSType) (target : TSType)
  | argumentCountMismatch (expected : Nat) (got : Nat)
  | notCallable (ty : TSType)
  | propertyNotFound (name : String) (ty : TSType)
  | identifierNotFound (name : String)
  | noReturnValue (funcName : String)
  | constraintNotSatisfied (typeArg : TSType) (constraint : TSType) (paramName : String)
  | wrongTypeArgCount (name : String) (expected : Nat) (got : Nat)
  | variableUsedBeforeAssignment (name : String)
  | cannotAssignToConstant (name : String)
  | cannotAssignToReadOnlyProperty (name : String)
  | invalidAssignmentTarget
  | thales (t : ThalesKind)

/-- Map diagnostic kind to tsc error code -/
def DiagnosticKind.tscCode : DiagnosticKind → Nat
  | .typeNotAssignable .. => 2322
  | .argumentTypeMismatch .. => 2345
  | .argumentCountMismatch .. => 2554
  | .notCallable .. => 2349
  | .propertyNotFound .. => 2339
  | .identifierNotFound .. => 2304
  | .noReturnValue .. => 2355
  | .constraintNotSatisfied .. => 2344
  | .wrongTypeArgCount .. => 2558
  | .variableUsedBeforeAssignment .. => 2454
  | .cannotAssignToConstant _ => 2588
  | .cannotAssignToReadOnlyProperty _ => 2540
  | .invalidAssignmentTarget => 2364
  | .thales _ => 0

/-- Format a human-readable message for the diagnostic -/
def DiagnosticKind.message : DiagnosticKind → String
  | .typeNotAssignable src tgt =>
    s!"Type '{formatType src}' is not assignable to type '{formatType tgt}'"
  | .argumentTypeMismatch _ src tgt =>
    s!"Argument of type '{formatType src}' is not assignable to parameter of type '{formatType tgt}'"
  | .argumentCountMismatch expected got =>
    s!"Expected {expected} arguments, but got {got}"
  | .notCallable ty =>
    s!"This expression is not callable. Type '{formatType ty}' has no call signatures"
  | .propertyNotFound name ty =>
    s!"Property '{name}' does not exist on type '{formatType ty}'"
  | .identifierNotFound name =>
    s!"Cannot find name '{name}'"
  | .noReturnValue _ =>
    s!"A function whose declared type is neither 'void' nor 'any' must return a value"
  | .constraintNotSatisfied arg constraint paramName =>
    s!"Type '{formatType arg}' does not satisfy the constraint '{formatType constraint}' for type parameter '{paramName}'"
  | .wrongTypeArgCount name expected got =>
    s!"Expected {expected} type arguments, but got {got} for type '{name}'"
  | .variableUsedBeforeAssignment name =>
    s!"Variable '{name}' is used before being assigned"
  | .cannotAssignToConstant name =>
    s!"Cannot assign to '{name}' because it is a constant"
  | .cannotAssignToReadOnlyProperty name =>
    s!"Cannot assign to '{name}' because it is a read-only property"
  | .invalidAssignmentTarget =>
    "The left-hand side of an assignment expression must be a variable or a property access"
  | .thales t => t.message

/-- A diagnostic with source location -/
structure Diagnostic where
  kind : DiagnosticKind
  location : Option SourceLocation := none

/-- Format a diagnostic for display: file(line,col): error TS2322: message.
    Columns are rendered 1-indexed (matching tsc's convention) even though
    the parser produces 0-indexed columns internally. -/
def Diagnostic.format (d : Diagnostic) (filename : String := "") : String :=
  let loc := match d.location with
    | some loc => s!"{filename}({loc.start.line},{loc.start.column + 1}): "
    | none => if filename.isEmpty then "" else s!"{filename}: "
  match d.kind with
  | .thales t => s!"{loc}error TH{padCode t.thCode}: {t.message}"
  | k => s!"{loc}error TS{k.tscCode}: {k.message}"

/-- Extract the TH code if this is a Thales-category diagnostic -/
def Diagnostic.thalesCode? (d : Diagnostic) : Option Nat :=
  match d.kind with
  | .thales t => some t.thCode
  | _ => none

end Thales.TypeCheck
