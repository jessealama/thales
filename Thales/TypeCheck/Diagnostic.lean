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
  | assignmentInExpressionPosition
  | mutationInThrowsContext (name : String)
  | loopNotSupported
  | asyncNotSupported
  | anyNotPermitted
  | unknownNotPermitted
  | unionMustBeDiscriminated
  | intersectionNotSupported
  | typeLevelProgrammingNotSupported
  | nullUndefinedNotSupported
  -- TH0026: condition positions and `!`/`&&`/`||` operands must be
  -- boolean; `requireBooleanCondition` has the rationale.
  | conditionNotBoolean (actualType : String)
  -- TH0030: unsupported class *form* (class expressions, abstract classes,
  -- generic classes, `implements` clauses). The v1 declaration shape
  -- (readonly fields, assign-each-field-once ctor, public instance methods)
  -- is in-subset; member-level violations draw TH0094-TH0102 below.
  | classNotSupported (form : String)
  | inheritanceNotSupported
  -- Class member-form diagnostics (TH0094-TH0102)
  | classAccessorNotSupported
  | classStaticNotSupported
  | classPrivateMemberNotSupported
  | classFieldInitializerNotSupported
  | classFieldFormNotSupported (detail : String)
  | classCtorFormNotSupported (detail : String)
  | classMethodFormNotSupported (detail : String)
  | classMethodForwardReference (name : String)
  | classMethodUsedAsValue (name : String)
  | switchNotExhaustive (missingKinds : List String)
  | switchNotLowerable
  | shadowingNotSupported (name : String)
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
  -- TH0068: while/do-while (and while-desugared `for`) lower to a
  -- partial-backed combinator the termination verifier cannot see through,
  -- so they cannot substantiate a `@total` claim.
  | totalHasUnverifiableLoop
  | totalityUnverified (leanError : String)
  -- Refinement-type diagnostics (TH0080–TH0081)
  | literalOutOfRange (literal : Float) (typeName : String) (min : Option Float) (max : Option Float)
  | refinementNeedsEvidence (sourceName : String) (targetTypeName : String)
  -- Computed-index diagnostics (TH0082–TH0083)
  | possiblyUndefinedOperand
  | computedIndexNotArray
  | definednessTestUnrecordedBinding
  -- Array stdlib-method diagnostic (TH0085); `receiverIsArray` is false when
  -- the receiver's type could not be resolved, so the message must not
  -- assert array-hood
  | arrayMethodReceiverNotLowerable (methodName : String) (receiverIsArray : Bool)
  -- Definedness test on a non-identifier subject (TH0086)
  | definednessTestNonIdentifierSubject
  -- Unsupported String.prototype method (TH0087)
  | stringMethodNotSupported (methodName : String)
  -- Unsupported ESM import/export forms and import cycles (TH0088–TH0090)
  | unsupportedImportForm (form : String)
  | unsupportedExportForm (form : String)
  | importCycle (cyclePath : String)
  -- Regex literal in value position (TH0091)
  | regexLiteral
  -- Unsupported unary operator (TH0092): typeof/void/delete, in any position
  | unsupportedUnaryOperator (op : String)
  -- TH0093: a hoisted top-level declaration references a top-level mutable
  -- `let` (which lowers to a `main`-local binding the declaration cannot see)
  | topLevelMutableReferencedByHoisted (name : String)
  -- TH0103: the emitter lowers the `undefined` global to `.none`, so a
  -- user binding named `undefined` would be silently rewritten
  | undefinedBindingName
  -- TH0104: a bare null/undefined initializer with no annotation gives
  -- the lowered `.none` no element type to elaborate at
  | nullishInitializerNeedsAnnotation
  -- TH0105: tsc accepts forward references to hoisted declarations, but
  -- emitted Lean declarations appear in source order
  | referencedBeforeDeclaration (name : String)
  -- Directive diagnostics (TH9000–TH9003)
  | directiveUnused
  | directiveCodeMismatch (expected : Nat) (actual : List Nat)
  | emissionBlockedBySuppressedViolation
  | directiveMalformed
  -- Emit-soundness diagnostic (TH9004)
  | emittedCodeContainsSorry (filename : String)
  -- Emit-soundness diagnostic (TH9005): emitter produced an unlowerable
  -- placeholder. Untriggerable from valid TS by design (subset checks reject
  -- first); a firing means a genuine, previously-unknown subset gap.
  | emittedCodeContainsUnsupported (reasons : String)
  deriving Repr

/-- Map a ThalesKind to its numeric TH code -/
def ThalesKind.thCode : ThalesKind → Nat
  | .cannotReassignVariable _ => 1
  | .cannotAssignArrayElement => 2
  | .cannotAssignObjectProperty => 3
  | .cannotCallMutatingMethod _ => 4
  | .cannotMutateCapturedVariable _ => 5
  | .assignmentInExpressionPosition => 6
  | .mutationInThrowsContext _ => 7
  | .loopNotSupported => 10
  | .asyncNotSupported => 12
  | .anyNotPermitted => 20
  | .unknownNotPermitted => 21
  | .unionMustBeDiscriminated => 22
  | .intersectionNotSupported => 23
  | .typeLevelProgrammingNotSupported => 24
  | .nullUndefinedNotSupported => 25
  | .conditionNotBoolean _ => 26
  | .classNotSupported _ => 30
  | .inheritanceNotSupported => 31
  | .classAccessorNotSupported => 94
  | .classStaticNotSupported => 95
  | .classPrivateMemberNotSupported => 96
  | .classFieldInitializerNotSupported => 97
  | .classFieldFormNotSupported _ => 98
  | .classCtorFormNotSupported _ => 99
  | .classMethodFormNotSupported _ => 100
  | .classMethodForwardReference _ => 101
  | .classMethodUsedAsValue _ => 102
  | .switchNotExhaustive _ => 40
  | .switchNotLowerable => 41
  | .shadowingNotSupported _ => 32
  | .cannotVerifyTermination _ => 50
  | .unannotatedThrow _ => 60
  | .nonRecordThrow => 63
  | .throwsRequiresTypeList => 65
  | .totalConflictsWithThrows => 66
  | .totalHasUncaughtThrow _ => 67
  | .totalHasUnverifiableLoop => 68
  | .totalityUnverified _ => 70
  | .literalOutOfRange .. => 80
  | .refinementNeedsEvidence .. => 81
  | .possiblyUndefinedOperand => 82
  | .computedIndexNotArray => 83
  | .definednessTestUnrecordedBinding => 84
  | .arrayMethodReceiverNotLowerable .. => 85
  | .definednessTestNonIdentifierSubject => 86
  | .stringMethodNotSupported _ => 87
  | .unsupportedImportForm _ => 88
  | .unsupportedExportForm _ => 89
  | .importCycle _ => 90
  | .regexLiteral => 91
  | .unsupportedUnaryOperator _ => 92
  | .topLevelMutableReferencedByHoisted _ => 93
  | .undefinedBindingName => 103
  | .nullishInitializerNeedsAnnotation => 104
  | .referencedBeforeDeclaration _ => 105
  | .directiveUnused => 9000
  | .directiveCodeMismatch .. => 9001
  | .emissionBlockedBySuppressedViolation => 9002
  | .directiveMalformed => 9003
  | .emittedCodeContainsSorry _ => 9004
  | .emittedCodeContainsUnsupported _ => 9005

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
  | .assignmentInExpressionPosition =>
    "Assignment and update expressions are only supported as statements; assign in a separate statement"
  | .mutationInThrowsContext name =>
    s!"Cannot mutate variable '{name}' inside a `@throws` function or `try`/`catch`"
  | .loopNotSupported => "Loop not supported; use recursion or array methods"
  | .asyncNotSupported => "async/await not supported"
  | .anyNotPermitted => "'any' is not permitted"
  | .unknownNotPermitted => "'unknown' is not permitted in user code"
  | .unionMustBeDiscriminated => "Union must be discriminated (requires shared string-literal 'kind' field)"
  | .intersectionNotSupported => "Intersection types are not supported"
  | .typeLevelProgrammingNotSupported => "keyof/conditional/mapped types are not supported"
  | .nullUndefinedNotSupported => "null/undefined types are not supported; use Option<T>"
  | .conditionNotBoolean actualType =>
    s!"Condition must be boolean, got '{actualType}'; truthiness is not mirrored — compare explicitly (e.g. `x !== 0`)"
  | .classNotSupported form => s!"{form} are not supported"
  | .inheritanceNotSupported => "Inheritance ('extends') is not supported"
  | .classAccessorNotSupported => "Class accessors (get/set) are not supported"
  | .classStaticNotSupported => "Static class members are not supported"
  | .classPrivateMemberNotSupported => "Private class members are not supported"
  | .classFieldInitializerNotSupported =>
    "Class field initializers are not supported; assign the field in the constructor"
  | .classFieldFormNotSupported detail => s!"Unsupported class field: {detail}"
  | .classCtorFormNotSupported detail => s!"Unsupported constructor: {detail}"
  | .classMethodFormNotSupported detail => s!"Unsupported class method: {detail}"
  | .classMethodForwardReference name =>
    s!"Class method '{name}' is referenced before its declaration"
  | .classMethodUsedAsValue name =>
    s!"Class method '{name}' may only be called, not used as a value"
  | .switchNotExhaustive missingKinds =>
    s!"Non-exhaustive switch on discriminated union (missing: {String.intercalate ", " missingKinds})"
  | .switchNotLowerable =>
    "Switch not supported here: dispatch on a discriminated-union field (e.g. `switch (shape.kind)`) with every arm ending in `return`"
  | .shadowingNotSupported name =>
    s!"Declaration of '{name}' shadows a binding from an enclosing scope; rename the inner binding"
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
  | .totalHasUnverifiableLoop =>
    "`@total` function contains a loop whose termination cannot be verified; use a for-of loop or recursion, or remove `@total`"
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
  | .possiblyUndefinedOperand =>
    "Operand may be 'undefined' or 'null'; narrow it first (e.g. bind it and test `!== undefined`)"
  | .computedIndexNotArray =>
    "Computed index access is only supported on array values"
  | .definednessTestUnrecordedBinding =>
    "Cannot determine whether this binding may be 'undefined'; annotate it or bind it from a recognized initializer before testing it"
  | .arrayMethodReceiverNotLowerable methodName true =>
    s!"Array method '{methodName}' is only supported on a `number[]` or `string[]` receiver"
  | .arrayMethodReceiverNotLowerable methodName false =>
    s!"'{methodName}' is only supported when the receiver is statically a `number[]` or `string[]` variable; this receiver's type cannot be resolved"
  | .definednessTestNonIdentifierSubject =>
    "A definedness test against 'undefined'/'null' is only supported when its subject is a variable; bind this expression to a variable first"
  | .stringMethodNotSupported methodName =>
    s!"String method '{methodName}' is not supported; the available string operations are 'startsWith', 'endsWith', and 'split'"
  | .unsupportedImportForm form =>
    s!"This import form ({form}) is not supported; use named imports like " ++ "`import { a, b } from './m'`"
  | .unsupportedExportForm form =>
    s!"This export form ({form}) is not supported; use inline `export` on a declaration or " ++ "`export { a, b };`"
  | .importCycle cyclePath =>
    s!"Circular imports are not supported because the emitted Lean modules cannot form an import cycle ({cyclePath})"
  | .regexLiteral =>
    "Regex literals are not supported"
  | .unsupportedUnaryOperator op =>
    s!"The '{op}' operator is not supported"
  | .topLevelMutableReferencedByHoisted name =>
    s!"Top-level mutable variable '{name}' cannot be referenced by a hoisted declaration (function or const)"
  | .undefinedBindingName =>
    "The name 'undefined' cannot be bound; rename this binding"
  | .nullishInitializerNeedsAnnotation =>
    "A bare 'null' or 'undefined' initializer needs a type annotation on the binding"
  | .referencedBeforeDeclaration name =>
    s!"'{name}' is referenced before its declaration; move the declaration before this use"
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
  | .emittedCodeContainsUnsupported reasons =>
    s!"Internal: the emitter produced unlowerable construct(s) ({reasons}); this is a subset gap — the program was accepted but cannot be emitted. Please report it."

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
  -- Module resolution diagnostics mirroring tsc (ESM imports)
  | moduleNotFound (spec : String)                 -- TS2307
  | noExportedMember (modName : String) (name : String)  -- TS2305
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
  | .moduleNotFound _ => 2307
  | .noExportedMember .. => 2305
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
  | .moduleNotFound spec =>
    s!"Cannot find module '{spec}' or its corresponding type declarations."
  | .noExportedMember modName name =>
    s!"Module '\"{modName}\"' has no exported member '{name}'."
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
