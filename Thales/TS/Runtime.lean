/-
  Thales/TS/Runtime.lean
  Lean-side runtime for code emitted by `thales`.
  Mirrors the Thales-TS surface stdlib in Lean shape.
-/

set_option autoImplicit false

namespace Thales.TS

/-- The largest exact integer representable as a Float (`2^53 − 1`),
    matching JS `Number.MAX_SAFE_INTEGER`. -/
def Float.maxSafeInteger : Float := 9007199254740991.0

/-- Predicate: `x` is an integer-valued, finite float. Mirrors JS
    `Number.isInteger(x)`. NOT same as `isSafeInteger` (no range check). -/
def Float.isInteger (x : Float) : Bool :=
  x.isFinite && x == x.floor

/-- Predicate: `x` is a safe integer. Mirrors JS `Number.isSafeInteger(x)`. -/
def Float.isSafeInteger (x : Float) : Bool :=
  x.isFinite && x == x.floor && x.abs ≤ Float.maxSafeInteger

/-- Predicate guard for `Integer`. Same as `Float.isSafeInteger`. -/
def isInteger (x : Float) : Bool := Float.isSafeInteger x

/-- Predicate guard for `Natural`. Nested: `isInteger ∧ x ≥ 0`. -/
def isNatural (x : Float) : Bool := isInteger x && x ≥ 0.0

/-- Predicate guard for `Byte`. Nested: `isNatural ∧ x ≤ 255`. -/
def isByte (x : Float) : Bool := isNatural x && x ≤ 255.0

/-- Predicate guard for `Bit`. Nested: `isByte ∧ (x = 0 ∨ x = 1)`.
    The `isByte` conjunct is logically redundant on inputs satisfying
    the disjunction (both 0 and 1 are bytes), but the nesting makes
    the coercion `Bit → Byte` provable as a one-line lemma. -/
def isBit (x : Float) : Bool := isByte x && (x == 0.0 || x == 1.0)

/-- Refinement type: safe integer. -/
abbrev Integer := { x : Float // isInteger x = true }

/-- Refinement type: non-negative safe integer. -/
abbrev Natural := { x : Float // isNatural x = true }

/-- Refinement type: integer in `[0, 255]`. -/
abbrev Byte := { x : Float // isByte x = true }

/-- Refinement type: `0` or `1` (and `-0` per IEEE 754). -/
abbrev Bit := { x : Float // isBit x = true }

/-- `isBit x → isByte x` (one-line proof from nesting). -/
theorem isByte_of_isBit {x : Float} (h : isBit x = true) : isByte x = true := by
  unfold isBit at h
  exact (Bool.and_eq_true _ _).mp h |>.1

/-- `isByte x → isNatural x`. -/
theorem isNatural_of_isByte {x : Float} (h : isByte x = true) : isNatural x = true := by
  unfold isByte at h
  exact (Bool.and_eq_true _ _).mp h |>.1

/-- `isNatural x → isInteger x`. -/
theorem isInteger_of_isNatural {x : Float} (h : isNatural x = true) : isInteger x = true := by
  unfold isNatural at h
  exact (Bool.and_eq_true _ _).mp h |>.1

instance : Coe Bit Byte := ⟨fun b => ⟨b.val, isByte_of_isBit b.property⟩⟩
instance : Coe Byte Natural := ⟨fun b => ⟨b.val, isNatural_of_isByte b.property⟩⟩
instance : Coe Natural Integer := ⟨fun n => ⟨n.val, isInteger_of_isNatural n.property⟩⟩
instance : Coe Integer Float := ⟨Subtype.val⟩

/-- `Inhabited` instances for the refinement types so that `panic!` in
    the throwing constructors typechecks. The default value is `0`,
    which satisfies all four predicates. -/
instance : Inhabited Integer := ⟨⟨0.0, by native_decide⟩⟩
instance : Inhabited Natural := ⟨⟨0.0, by native_decide⟩⟩
instance : Inhabited Byte := ⟨⟨0.0, by native_decide⟩⟩
instance : Inhabited Bit := ⟨⟨0.0, by native_decide⟩⟩

/-- Throwing constructor for `Integer`. Panics if `x` is not a safe integer. -/
def asInteger (x : Float) : Integer :=
  if h : isInteger x = true then ⟨x, h⟩
  else panic! s!"not an integer: {x}"

def asNatural (x : Float) : Natural :=
  if h : isNatural x = true then ⟨x, h⟩
  else panic! s!"not a natural: {x}"

def asByte (x : Float) : Byte :=
  if h : isByte x = true then ⟨x, h⟩
  else panic! s!"not a byte: {x}"

def asBit (x : Float) : Bit :=
  if h : isBit x = true then ⟨x, h⟩
  else panic! s!"not a bit: {x}"

/-- IO-typed mirrors used at side-effect positions (`asInteger(x);` as a
    statement). On failure they print a `RangeError` line and exit 1,
    matching tsx's behaviour. -/
private def rangeCheckEffect (label : String) (ok : Bool) (x : Float) : IO Unit := do
  if ok then pure ()
  else
    IO.eprintln s!"RangeError: not {label}: {x}"
    IO.Process.exit 1

def asIntegerEffect (x : Float) : IO Unit := rangeCheckEffect "an integer" (isInteger x) x
def asNaturalEffect (x : Float) : IO Unit := rangeCheckEffect "a natural" (isNatural x) x
def asByteEffect    (x : Float) : IO Unit := rangeCheckEffect "a byte"    (isByte x)    x
def asBitEffect     (x : Float) : IO Unit := rangeCheckEffect "a bit"     (isBit x)     x

/-- Convert a `Natural` to `Nat`. The round-trip is exact for non-negative
    safe-integer Floats (see `Float.toUInt64_of_isNatural`). -/
def Natural.toNat (n : Natural) : Nat := n.val.toUInt64.toNat

/-- Reflect a safe-integer-valued `Integer` into Lean `Int`.
    The proof comes from `x.property`. -/
def Integer.toInt (x : Integer) : Int :=
  if x.val ≥ 0.0 then (x.val.toUInt64.toNat : Int)
  else -((-x.val).toUInt64.toNat : Int)

/-! ## Float↔Int boundary axioms

These postulate the IEEE-754 facts about `Float.toUInt64`, `Nat.toFloat`,
and float negation that Lean's stdlib does not state directly. They are
reasoned from IEEE-754 first principles: negation flips the sign bit
exactly, and `Nat.toFloat` is exact for any `n ≤ MAX_SAFE_INTEGER`. -/

axiom Nat.toFloat_isSafeInteger (n : Nat) (h : n ≤ 9007199254740991) :
  Float.isSafeInteger n.toFloat = true

axiom Float.neg_isSafeInteger (x : Float) (h : Float.isSafeInteger x = true) :
  Float.isSafeInteger (-x) = true

/-- Lift an in-range `Int` into `Integer`, going through `Nat.toFloat`
    (and a sign flip for negatives). -/
def Integer.ofInt (n : Int) (h : n.natAbs ≤ 9007199254740991) : Integer :=
  ⟨if n < 0 then -((n.natAbs).toFloat) else (n.natAbs).toFloat,
    by
      show isInteger _ = true
      unfold isInteger
      split
      · exact Float.neg_isSafeInteger _ (Nat.toFloat_isSafeInteger _ h)
      · exact Nat.toFloat_isSafeInteger _ h⟩

axiom Float.ofInt_neg (n : Int) (h : n.natAbs ≤ 9007199254740991) :
  (Integer.ofInt (-n) (by simpa using h)).val = -((Integer.ofInt n h).val)

axiom Float.ofInt_lt (m n : Int) (hm : m.natAbs ≤ 9007199254740991)
    (hn : n.natAbs ≤ 9007199254740991) :
  (Integer.ofInt m hm).val < (Integer.ofInt n hn).val ↔ m < n

axiom Float.ofInt_le (m n : Int) (hm : m.natAbs ≤ 9007199254740991)
    (hn : n.natAbs ≤ 9007199254740991) :
  (Integer.ofInt m hm).val ≤ (Integer.ofInt n hn).val ↔ m ≤ n

/-- Round-trip: a Float satisfying `isNatural` converts to UInt64 and
    back to Float losslessly. Load-bearing for `Natural.toNat`'s
    soundness. -/
axiom Float.toUInt64_of_isNatural (x : Float) (h : isNatural x = true) :
  x.toUInt64.toNat.toFloat = x

/-- `Nat.toFloat` is non-negative. -/
axiom Nat.toFloat_nonneg (n : Nat) : n.toFloat ≥ 0.0

/-- Embed a `String`'s `length` as a `Natural`. -/
def String.toNaturalLength (s : String) : Natural :=
  if h : s.length ≤ 9007199254740991 then
    ⟨s.length.toFloat,
      by
        show isNatural _ = true
        unfold isNatural
        rw [Bool.and_eq_true]
        refine ⟨Nat.toFloat_isSafeInteger _ h, ?_⟩
        exact decide_eq_true (Nat.toFloat_nonneg s.length)⟩
  else
    panic! "string length exceeds MAX_SAFE_INTEGER"

/-- Embed an `Array`'s `size` as a `Natural`. Panics on arrays larger than
    `MAX_SAFE_INTEGER`. -/
def Array.toNaturalSize {α : Type} (xs : Array α) : Natural :=
  if h : xs.size ≤ 9007199254740991 then
    ⟨xs.size.toFloat,
      by
        show isNatural _ = true
        unfold isNatural
        rw [Bool.and_eq_true]
        refine ⟨Nat.toFloat_isSafeInteger _ h, ?_⟩
        exact decide_eq_true (Nat.toFloat_nonneg xs.size)⟩
  else
    panic! "array size exceeds MAX_SAFE_INTEGER"

/-! ## Reflection theorems

Round-trip identity for `toInt`/`ofInt` plus add/sub/mul homomorphisms.
Postulated as axioms: the underlying Float-Int round-trip and IEEE-754
exactness on safe-integer inputs are not provable in the stdlib. -/

axiom Integer.toInt_ofInt (n : Int) (h : n.natAbs ≤ 9007199254740991) :
  (Integer.ofInt n h).toInt = n

axiom Integer.add_homomorphism
    (x y : Integer)
    (hsum : isInteger (x.val + y.val) = true) :
  Integer.toInt ⟨x.val + y.val, hsum⟩ = x.toInt + y.toInt

axiom Integer.sub_homomorphism
    (x y : Integer)
    (hdiff : isInteger (x.val - y.val) = true) :
  Integer.toInt ⟨x.val - y.val, hdiff⟩ = x.toInt - y.toInt

axiom Integer.mul_homomorphism
    (x y : Integer)
    (hprod : isInteger (x.val * y.val) = true) :
  Integer.toInt ⟨x.val * y.val, hprod⟩ = x.toInt * y.toInt

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

/-- Typeclass for values printable by `console.log`. Instances cover the
    JS ToString cases the conformance suite exercises. -/
class JSShow (α : Type) where
  jsShow : α → String

instance : JSShow Float := ⟨jsNumberToString⟩
/-- Refinement subtypes of Float print like their underlying value. -/
instance {p : Float → Bool} : JSShow {x : Float // p x = true} :=
  ⟨fun x => jsNumberToString x.val⟩
-- `Option α` is the lowering of TS `T | undefined`; `none` prints as `undefined`.
instance {α : Type} [JSShow α] : JSShow (Option α) := ⟨fun
  | .none => "undefined"
  | .some v => JSShow.jsShow v⟩
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
    post-processing by the conformance harness. -/
def consoleLog {α : Type} [JSShow α] (x : α) : IO Unit :=
  IO.println (JSShow.jsShow x)

/-- Multi-argument `console.log(a, b, c)` prints space-separated values
    followed by a newline. Callers pre-render each argument via
    `JSShow.jsShow` so this only sees `String`s. -/
def consoleLogN (parts : List String) : IO Unit :=
  IO.println (String.intercalate " " parts)

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

/-- IEEE-754: `Float.abs` flips the sign bit only, preserving safe-integer-ness. -/
axiom Float.abs_isSafeInteger {x : Float} (h : Thales.TS.isInteger x = true) :
  Thales.TS.isInteger x.abs = true

/-- `Float.abs` is non-negative. -/
axiom Float.abs_nonneg (x : Float) : x.abs ≥ 0.0

namespace Math
  def abs (x : Float) : Float := x.abs
  def floor (x : Float) : Float := x.floor
  def ceil (x : Float) : Float := x.ceil
  def round (x : Float) : Float := (x + 0.5).floor
  def sqrt (x : Float) : Float := x.sqrt
  def min (x y : Float) : Float := if x ≤ y then x else y
  def max (x y : Float) : Float := if x ≥ y then x else y

  /-- `Math.abs` overload: absolute value of an `Integer` is a `Natural`. -/
  def absI (x : Integer) : Natural :=
    ⟨x.val.abs, by
      show isNatural _ = true
      unfold isNatural
      rw [Bool.and_eq_true]
      exact ⟨Float.abs_isSafeInteger x.property, decide_eq_true (Float.abs_nonneg x.val)⟩⟩
end Math

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
