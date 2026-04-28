/-
  Thales/TS/Runtime.lean
  Lean-side runtime for code emitted by `thales`.
  Mirrors the Thales-TS surface stdlib in Lean shape.
-/

set_option autoImplicit false

namespace Thales.TS

/-- Optional value. TS surface `Option<T>` translates to Lean's `Option`. -/
abbrev Option' := Option

/-- Result type. TS surface `Result<T, E>` is a tagged union
    `{ok: true, value: T} | {ok: false, error: E}`. Emitted as Lean's
    built-in `Except` in most cases; this named alias makes emitted code
    easier to read and keeps an `.ok` / `.err` constructor vocabulary. -/
inductive Result (α β : Type) where
  | ok (value : α)
  | err (error : β)
  deriving Repr, BEq

namespace Result
  def map {α β γ : Type} (f : α → γ) : Result α β → Result γ β
    | .ok v => .ok (f v)
    | .err e => .err e

  def mapErr {α β γ : Type} (f : β → γ) : Result α β → Result α γ
    | .ok v => .ok v
    | .err e => .err (f e)

  def andThen {α β γ : Type} (f : α → Result γ β) : Result α β → Result γ β
    | .ok v => f v
    | .err e => .err e

  def isOk {α β : Type} : Result α β → Bool
    | .ok _ => true
    | .err _ => false

  def isErr {α β : Type} : Result α β → Bool
    | .ok _ => false
    | .err _ => true
end Result

/-- Safe array indexing. TS surface: `arr[i]` in Thales-TS returns `Option<T>`. -/
@[inline] def Array.get? {α : Type} (arr : Array α) (i : Nat) : Option α := arr[i]?

/-- Strip trailing zeros from the fractional part of a `Float.toString` output,
    and drop the dot if nothing remains. `"42.000000" → "42"`,
    `"12.560000" → "12.56"`. -/
private def stripTrailingZerosAfterDot (s : String) : String :=
  match s.splitOn "." with
  | [whole, frac] =>
      let fracChars := frac.toList.reverse.dropWhile (· == '0') |>.reverse
      if fracChars.isEmpty then whole else s!"{whole}.{String.ofList fracChars}"
  | _ => s

/-- JS `Number.prototype.toString()` for the common cases Thales-TS v1 cares
    about. Whole-valued Floats print without a decimal; fractional Floats
    strip trailing zeros. Does not implement the full ECMA-262 ToString
    algorithm: very small or very large numbers (where JS uses exponential
    form) fall through to Lean's `%f` formatting. -/
def jsNumberToString (x : Float) : String :=
  if x.isNaN then "NaN"
  else if x == 0.0 then "0"
  else stripTrailingZerosAfterDot (toString x)

/-- Typeclass for values printable by `console.log`. Instances implement the
    small subset of JS ToString semantics v1 actually exercises. -/
class JSShow (α : Type) where
  jsShow : α → String

instance : JSShow Float  := ⟨jsNumberToString⟩
/-- TS `bigint` is emitted as Lean `Int`. JS's `console.log` on a bigint
    renders the decimal followed by an `n` suffix (e.g. `5n`, `-3n`, `0n`),
    matching `BigInt.prototype.toString` with the literal-form marker that
    `console.log` adds. -/
instance : JSShow Int    := ⟨fun n => toString n ++ "n"⟩
instance : JSShow Nat    := ⟨toString⟩
instance : JSShow String := ⟨id⟩
instance : JSShow Bool   := ⟨fun b => if b then "true" else "false"⟩

/-- Emitted counterpart of JS `console.log(x)`. Prints `x` using
    `JSShow.jsShow` so the Lean path's stdout matches the VM's without any
    post-processing by the examples runner. -/
def consoleLog {α : Type} [JSShow α] (x : α) : IO Unit :=
  IO.println (JSShow.jsShow x)

/-- Built-in JS error types as flat records.
    These are the types TS programmers reference in `@throws` annotations.
    Emitted Lean code opens this namespace (or uses fully-qualified names)
    so that `Error`, `TypeError`, etc. resolve without qualification. -/
structure Error where
  message : String
  deriving Repr, DecidableEq

structure TypeError where
  message : String
  deriving Repr, DecidableEq

structure RangeError where
  message : String
  deriving Repr, DecidableEq

structure SyntaxError where
  message : String
  deriving Repr, DecidableEq

structure ReferenceError where
  message : String
  deriving Repr, DecidableEq

/-- JS `parseFloat(s)` — parse a string to a Float.
    Supports integer strings and simple decimal strings. Returns `0/0` (NaN) for
    strings that cannot be parsed, mirroring JS behaviour for the common cases. -/
def parseFloat (s : String) : Float :=
  -- Try integer first
  if let some n := s.toNat? then n.toFloat
  else
    -- Try simple decimal: optional leading -, digits, optional .digits
    let (negative, rest) :=
      if s.startsWith "-" then (true, s.splitOn "-" |>.getLast?.getD "") else (false, s)
    let parts := rest.splitOn "."
    match parts with
    | [whole, frac] =>
        match whole.toNat?, frac.toNat? with
        | some w, some f =>
            let fracFloat := (f.toFloat) / (Float.pow 10.0 frac.length.toFloat)
            let absVal := w.toFloat + fracFloat
            if negative then -absVal else absVal
        | _, _ => 0.0 / 0.0  -- NaN
    | [whole] =>
        match whole.toNat? with
        | some n => if negative then -(n.toFloat) else n.toFloat
        | none => 0.0 / 0.0  -- NaN
    | _ => 0.0 / 0.0  -- NaN

/-- JS `isNaN(x)` — true iff the value is `NaN`. -/
def isNaN (x : Float) : Bool := x.isNaN

end Thales.TS

namespace Thales.TS.ArrayOps
  @[inline] def map {α β : Type} (arr : Array α) (f : α → β) : Array β := arr.map f
  @[inline] def filter {α : Type} (arr : Array α) (p : α → Bool) : Array α := arr.filter p
  @[inline] def reduce {α β : Type} (arr : Array α) (init : β) (f : β → α → β) : β := arr.foldl f init
  @[inline] def concat {α : Type} (a b : Array α) : Array α := a ++ b
  @[inline] def length {α : Type} (arr : Array α) : Nat := arr.size
  def slice {α : Type} (arr : Array α) (start stop : Nat) : Array α :=
    let lo := min start arr.size
    let hi := min stop arr.size
    if hi ≤ lo then #[] else
      arr.toList.drop lo |>.take (hi - lo) |> Array.mk
end Thales.TS.ArrayOps
