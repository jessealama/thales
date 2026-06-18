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

/-- IO-typed mirrors of the throwing constructors. The pure forms above
    are used inside type-level positions (e.g. when initializing a
    refinement-typed binding); these IO mirrors are emitted at side-effect
    positions (a bare `asInteger(x);` statement). They print a RangeError
    line on stderr and call `IO.Process.exit 1` so the harness's
    throw-iff equivalence check sees the same nonzero exit as `tsx`. -/
def asIntegerEffect (x : Float) : IO Unit := do
  if isInteger x then pure ()
  else
    IO.eprintln s!"RangeError: not an integer: {x}"
    IO.Process.exit 1

def asNaturalEffect (x : Float) : IO Unit := do
  if isNatural x then pure ()
  else
    IO.eprintln s!"RangeError: not a natural: {x}"
    IO.Process.exit 1

def asByteEffect (x : Float) : IO Unit := do
  if isByte x then pure ()
  else
    IO.eprintln s!"RangeError: not a byte: {x}"
    IO.Process.exit 1

def asBitEffect (x : Float) : IO Unit := do
  if isBit x then pure ()
  else
    IO.eprintln s!"RangeError: not a bit: {x}"
    IO.Process.exit 1


/-- Reflect a safe-integer-valued `Integer` into Lean `Int`.
    The proof comes from `x.property`. -/
def Integer.toInt (x : Integer) : Int :=
  if x.val ≥ 0.0 then (x.val.toUInt64.toNat : Int)
  else -((-x.val).toUInt64.toNat : Int)

/-! ## Float↔Int boundary axioms

These axioms are the irreducible Float-Int IEEE-754 boundary
relationships that Lean's standard `Float` library does not give us.
Three of them (`ofInt_neg`, `ofInt_lt`, `ofInt_le`) were validated
by the `feat/thales-grind-poc` branch. Two more
(`Nat.toFloat_isSafeInteger`, `Float.neg_isSafeInteger`) are
load-bearing for `Integer.ofInt`. They are reasoned from IEEE 754
first principles.

`Nat.toFloat_isSafeInteger` and `Float.neg_isSafeInteger` are
declared first because `Integer.ofInt` depends on them in its
proof obligation. The `ofInt_*` axioms (which mention
`Integer.ofInt`) follow the definition. -/

/-- Any `Nat` bounded by `MAX_SAFE_INTEGER` converts to a Float that
    is a safe integer. The standard library's `Nat.toFloat` is
    surjective onto integer-valued safe-range Floats and is exact in
    this range, but Lean's stdlib does not state this; we postulate
    it as an IEEE-754 boundary axiom. -/
axiom Nat.toFloat_isSafeInteger (n : Nat) (h : n ≤ 9007199254740991) :
  Float.isSafeInteger n.toFloat = true

/-- Negating a safe-integer-valued Float preserves `isSafeInteger`.
    IEEE-754 negation flips the sign bit and is exact, so finiteness,
    integer-valuedness, and the absolute-value bound are preserved. -/
axiom Float.neg_isSafeInteger (x : Float) (h : Float.isSafeInteger x = true) :
  Float.isSafeInteger (-x) = true

/-- Lift an in-range `Int` into `Integer`. The witness is built from a
    Nat-to-Float conversion. The proof goes through
    `Nat.toFloat_isSafeInteger` and `Float.neg_isSafeInteger`:
    `n.toFloat` is a safe integer for any `n ≤ MAX_SAFE_INTEGER`,
    and negating a safe integer preserves `isSafeInteger`. -/
def Integer.ofInt (n : Int) (h : n.natAbs ≤ 9007199254740991) : Integer :=
  ⟨if n < 0 then -((n.natAbs).toFloat) else (n.natAbs).toFloat,
    by
      show isInteger _ = true
      unfold isInteger
      split
      · -- n < 0 branch: value is -(n.natAbs.toFloat).
        exact Float.neg_isSafeInteger _ (Nat.toFloat_isSafeInteger _ h)
      · -- n ≥ 0 branch: value is n.natAbs.toFloat.
        exact Nat.toFloat_isSafeInteger _ h⟩

axiom Float.ofInt_neg (n : Int) (h : n.natAbs ≤ 9007199254740991) :
  (Integer.ofInt (-n) (by simpa using h)).val = -((Integer.ofInt n h).val)

axiom Float.ofInt_lt (m n : Int) (hm : m.natAbs ≤ 9007199254740991)
    (hn : n.natAbs ≤ 9007199254740991) :
  (Integer.ofInt m hm).val < (Integer.ofInt n hn).val ↔ m < n

axiom Float.ofInt_le (m n : Int) (hm : m.natAbs ≤ 9007199254740991)
    (hn : n.natAbs ≤ 9007199254740991) :
  (Integer.ofInt m hm).val ≤ (Integer.ofInt n hn).val ↔ m ≤ n

/-- IEEE-754: embedding a `Nat` into `Float` always yields a
    non-negative value. Postulated alongside the other boundary axioms;
    no theorem in Lean's stdlib asserts this directly. -/
axiom Nat.toFloat_nonneg (n : Nat) : n.toFloat ≥ 0.0

/-- JS `+` on two strings is concatenation. The emitter lowers TS `+`
    uniformly to Lean `+`; this instance covers the String × String case.
    Mixed string/number `+` (JS coerces) deliberately
    has no instance — it fails loudly at the Lean stage rather than
    miscompiling. -/
instance : HAdd String String String := ⟨String.append⟩

/-- Embed a `String`'s `length` as a `Natural`. Same shape as
    `Array.toNaturalSize`; bounds the length at MAX_SAFE_INTEGER. -/
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

/-- Embed an `Array`'s `size` as a `Natural`. The proof composes
    `Nat.toFloat_isSafeInteger` (for the safe-integer-ness) with
    `Nat.toFloat_nonneg` (for the `≥ 0` half of `isNatural`). The
    safe-integer cap is in place because our embedding panics on
    arrays beyond MAX_SAFE_INTEGER — well outside any realistic v0.6
    program. -/
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

Round-trip identity for `toInt`/`ofInt`, plus add/sub/mul
homomorphisms. These are the user-facing reflection lemmas that
Thales-emitted Lean code uses to reason about safe-integer
arithmetic. Per the spec V2 §9, the boundary-axiom set is
permitted to expand when proofs from existing axioms are not
constructible in the pinned toolchain. The four statements below
are postulated as axioms because reasoning about
`Float.toUInt64.toNat` round-trips and IEEE 754 add/sub/mul
exactness on safe-integer inputs requires Float-Int internals
that Lean's stdlib does not expose. They are reasoned from
IEEE 754 first principles, same justification as the axioms
above. -/

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

/-- JS array element read: `xs[i]` with a `number` index. Fractional,
    negative, NaN, infinite, non-safe-integer, and out-of-bounds indices
    all read as `undefined` (`none`); `-0` reads element 0. The `isNatural`
    guard makes the `Float → Nat` conversion exact. -/
@[inline] def indexRead {α : Type} (xs : Array α) (i : Float) : Option α :=
  if isNatural i then xs[i.toUInt64.toNat]? else none

/-- Strip trailing zeros from the fractional part of a `Float.toString` output,
    and drop the dot if nothing remains. `"42.000000" → "42"`,
    `"12.560000" → "12.56"`. -/
private def stripTrailingZerosAfterDot (s : String) : String :=
  match s.splitOn "." with
  | [whole, frac] =>
      let fracChars := frac.toList.reverse.dropWhile (· == '0') |>.reverse
      if fracChars.isEmpty then whole else s!"{whole}.{String.ofList fracChars}"
  | _ => s

/-! ### JS numeric-conversion helpers (#32, used by #24's operators)

ES2023 7.1.6 ToInt32 / 7.1.7 ToUint32, and the `%`, bitwise, and shift
operators built on them. JS bitwise operates on the 32-bit integer
truncation of the double; shift counts mask to 5 bits; `%` keeps the
dividend's sign. -/

/-- ES ToUint32: truncate toward zero, wrap modulo 2^32. NaN/±∞ → 0.
    `|x| < 2^64` truncates exactly via `toUInt64`; larger magnitudes
    decompose as m·2^k through `frExp` (53-bit mantissa), so the wrap is
    exact for every double. -/
def toUint32 (x : Float) : Nat :=
  if x.isNaN || x.isInf then 0
  else
    let neg := x < 0.0
    let a := x.abs
    let n : Nat :=
      if a < 18446744073709551616.0 then -- 2^64
        a.toUInt64.toNat
      else
        let (frac, exp) := a.frExp
        -- a = frac·2^exp with frac ∈ [0.5, 1), so frac·2^53 is integral
        let m : Nat := (frac * 9007199254740992.0).toUInt64.toNat
        let k : Int := exp - 53
        if k ≥ 32 then 0
        else m <<< k.toNat
    let r := n % 4294967296
    if neg && r != 0 then 4294967296 - r else r

/-- ES ToInt32: ToUint32 reinterpreted as signed 32-bit. -/
def toInt32 (x : Float) : Int :=
  let u := toUint32 x
  if u ≥ 2147483648 then (u : Int) - 4294967296 else (u : Int)

/-- Reinterpret a Uint32 value as a signed 32-bit quantity, as Float. -/
private def int32ToFloat (u : Nat) : Float :=
  if u ≥ 2147483648 then Float.ofInt ((u : Int) - 4294967296) else Float.ofNat u

/-- JS `a & b`. -/
def jsBitAnd (a b : Float) : Float := int32ToFloat (toUint32 a &&& toUint32 b)
/-- JS `a | b`. -/
def jsBitOr (a b : Float) : Float := int32ToFloat (toUint32 a ||| toUint32 b)
/-- JS `a ^ b`. -/
def jsBitXor (a b : Float) : Float := int32ToFloat (toUint32 a ^^^ toUint32 b)
/-- JS `a << b` (count masked to 5 bits, result wraps to Int32). -/
def jsShl (a b : Float) : Float :=
  int32ToFloat ((toUint32 a <<< (toUint32 b % 32)) % 4294967296)
/-- JS `a >> b` (sign-propagating shift on the Int32 value). -/
def jsShr (a b : Float) : Float :=
  Float.ofInt (toInt32 a >>> (toUint32 b % 32))
/-- JS `a >>> b` (zero-fill shift on the Uint32 value; result is Uint32). -/
def jsUShr (a b : Float) : Float :=
  Float.ofNat (toUint32 a >>> (toUint32 b % 32))

/-- JS `%` (fmod): result has the dividend's sign. NaN when the divisor is
    ±0, the dividend is ±∞, or either operand is NaN; `a % ±∞ = a`.
    Computed as `|a| - |b|·⌊|a|/|b|⌋` with the dividend's sign re-applied;
    exact for the magnitudes v1 exercises (extreme-ratio rounding is
    tracked in the test262 baseline). -/
def jsMod (a b : Float) : Float :=
  if a.isNaN || b.isNaN || a.isInf || b == 0.0 then (0.0 / 0.0)
  else if b.isInf then a
  else if a == 0.0 then a
  else
    let q := (a / b).abs.floor
    let r := a.abs - b.abs * q
    if a < 0.0 then -r else r

/-- JS `Number.prototype.toString()` for the common cases Thales-TS v1 cares
    about. Whole-valued Floats print without a decimal; fractional Floats
    strip trailing zeros. Does not implement the full ECMA-262 ToString
    algorithm: very small or very large numbers (where JS uses exponential
    form) fall through to Lean's `%f` formatting. -/
def jsNumberToString (x : Float) : String :=
  if x.isNaN then "NaN"
  else if x.isInf then (if x < 0.0 then "-Infinity" else "Infinity")
  else if x == 0.0 then "0"
  else stripTrailingZerosAfterDot (toString x)

/-- JS global `NaN` as a Lean `Float` (the emitter lowers the `NaN` identifier
    here so it is never a bare, unresolved name). -/
def tsNaN : Float := 0.0 / 0.0

/-- JS global `Infinity` as a Lean `Float`; `-Infinity` lowers to its negation. -/
def tsInfinity : Float := 1.0 / 0.0

/-- Typeclass for values printable by `console.log`. Instances implement the
    small subset of JS ToString semantics v1 actually exercises. -/
class JSShow (α : Type) where
  jsShow : α → String

instance : JSShow Float   := ⟨jsNumberToString⟩
/-- Refinement subtypes of Float print the same as their underlying Float value.
    JS `console.log(42)` prints `42`, so `Integer`/`Natural`/`Byte`/`Bit` do too. -/
instance : JSShow Integer := ⟨fun x => jsNumberToString x.val⟩
instance : JSShow Natural := ⟨fun x => jsNumberToString x.val⟩
instance : JSShow Byte    := ⟨fun x => jsNumberToString x.val⟩
instance : JSShow Bit     := ⟨fun x => jsNumberToString x.val⟩
/-- TS `bigint` is emitted as Lean `Int`. JS's `console.log` on a bigint
    renders the decimal followed by an `n` suffix (e.g. `5n`, `-3n`, `0n`),
    matching `BigInt.prototype.toString` with the literal-form marker that
    `console.log` adds. -/
instance : JSShow Int    := ⟨fun n => toString n ++ "n"⟩
instance : JSShow Nat    := ⟨toString⟩
instance : JSShow String := ⟨id⟩
instance : JSShow Bool   := ⟨fun b => if b then "true" else "false"⟩

/-! ### Array stdlib methods (#28)

`join`/`indexOf`/`includes` for `number[]` (`Array Float`) and `string[]`
(`Array String`). The emitter dispatches on the receiver's element type. -/

/-- `Array.prototype.join`: stringify each element via `JSShow` and join with
    `sep`. Empty array → `""`. JS number→string goes through `jsNumberToString`,
    so output is byte-identical to Node. -/
def Array.joinJS {α : Type} [JSShow α] (xs : Array α) (sep : String) : String :=
  String.intercalate sep (xs.toList.map JSShow.jsShow)

/-- JS `ToIntegerOrInfinity` clamped to a search start offset `k`
    (`0 ≤ k ≤ len`) for the `indexOf`/`includes` `fromIndex` argument over an
    array of length `len`. `NaN → 0`; the value truncates toward zero; a
    negative `fromIndex` counts back from the end (`max(len + n, 0)`); a value
    at or beyond `len` starts past the end (empty search). -/
def Array.startIndexJS (len : Nat) (fromIndex : Float) : Nat :=
  if fromIndex.isNaN then 0
  else if fromIndex < 0.0 then
    let mag := -fromIndex
    if mag ≥ len.toFloat then 0 else len - mag.toUInt64.toNat
  else
    if fromIndex ≥ len.toFloat then len else fromIndex.toUInt64.toNat

/-- `Array.prototype.indexOf(x, fromIndex)`: first index `≥ fromIndex` whose
    element `=== x`, else `-1`, as a JS number (`Float`). Lean `Float` `BEq` is
    IEEE (`NaN ≠ NaN`, `+0 = -0`), matching JS strict equality; `String` `BEq`
    matches too. -/
def Array.indexOfFromJS {α : Type} [BEq α] (xs : Array α) (x : α) (fromIndex : Float) : Float :=
  let k := Array.startIndexJS xs.size fromIndex
  match (xs.toList.drop k).findIdx? (· == x) with
  | some i => (k + i).toFloat
  | none   => -1.0

/-- `Array.prototype.indexOf(x)`: the single-argument form (search from 0). -/
def Array.indexOfJS {α : Type} [BEq α] (xs : Array α) (x : α) : Float :=
  Array.indexOfFromJS xs x 0.0

/-- `Array.prototype.includes(x, fromIndex)` for numbers: SameValueZero from
    `fromIndex`, so `NaN` matches `NaN` (unlike `indexOf`) and `+0`/`-0`
    match. -/
def Array.includesFloatFrom (xs : Array Float) (x : Float) (fromIndex : Float) : Bool :=
  let tail := xs.toList.drop (Array.startIndexJS xs.size fromIndex)
  if x.isNaN then tail.any (·.isNaN) else tail.any (· == x)

/-- `Array.prototype.includes(x)` for numbers: the single-argument form. -/
def Array.includesFloat (xs : Array Float) (x : Float) : Bool :=
  Array.includesFloatFrom xs x 0.0

/-- `Array.prototype.includes(x, fromIndex)` for strings: structural equality
    (no NaN subtlety), searching from `fromIndex`. -/
def Array.includesStrFrom (xs : Array String) (x : String) (fromIndex : Float) : Bool :=
  (xs.toList.drop (Array.startIndexJS xs.size fromIndex)).any (· == x)

/-- `Array.prototype.includes(x)` for strings: the single-argument form. -/
def Array.includesStr (xs : Array String) (x : String) : Bool :=
  Array.includesStrFrom xs x 0.0

/-- `Array.prototype.findIndex(p)`: index of the first element satisfying `p`,
    else `-1`, as a JS number (`Float`). -/
def Array.findIndexJS {α : Type} (xs : Array α) (p : α → Bool) : Float :=
  match xs.toList.findIdx? p with
  | some i => i.toFloat
  | none   => -1.0

/-- The inclusive upper search bound `k` for `lastIndexOf(x, fromIndex)` over an
    array of length `len`: `NaN → 0`; truncate toward zero; non-negative values
    clamp to `len-1`; a negative `fromIndex` counts back from the end
    (`len + n`). `none` when the search window is empty (`len = 0` or the
    negative offset lands before index 0). -/
def Array.lastStartJS (len : Nat) (fromIndex : Float) : Option Nat :=
  if len == 0 then none
  else if fromIndex.isNaN then some 0
  else if fromIndex ≥ 0.0 then
    if fromIndex ≥ len.toFloat then some (len - 1)
    else some (min fromIndex.toUInt64.toNat (len - 1))
  else
    let magN := (-fromIndex).toUInt64.toNat
    if magN > len then none else some (len - magN)

/-- `Array.prototype.lastIndexOf(x, fromIndex)`: highest index `≤ fromIndex`
    whose element `=== x`, else `-1`. Same `===`/`Float` `BEq` semantics as
    `indexOf`. -/
def Array.lastIndexOfFromJS {α : Type} [BEq α] (xs : Array α) (x : α) (fromIndex : Float) : Float :=
  match Array.lastStartJS xs.size fromIndex with
  | none   => -1.0
  | some k =>
    -- search the prefix `0..k` from the top: reverse it, find the first match,
    -- and map the reversed position `j` back to the original index `k - j`.
    match ((xs.toList.take (k + 1)).reverse).findIdx? (· == x) with
    | some j => (k - j).toFloat
    | none   => -1.0

/-- `Array.prototype.lastIndexOf(x)`: the single-argument form (search from the
    last element). -/
def Array.lastIndexOfJS {α : Type} [BEq α] (xs : Array α) (x : α) : Float :=
  Array.lastIndexOfFromJS xs x (xs.size.toFloat - 1.0)

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

namespace Math
  def abs (x : Float) : Float := x.abs
  def floor (x : Float) : Float := x.floor
  def ceil (x : Float) : Float := x.ceil
  def round (x : Float) : Float := (x + 0.5).floor
  def sqrt (x : Float) : Float := x.sqrt
  def min (x y : Float) : Float := if x ≤ y then x else y
  def max (x y : Float) : Float := if x ≥ y then x else y

end Math

/-- Float.abs preserves `isSafeInteger` (and therefore `isInteger`). The
    underlying IEEE-754 abs operation flips the sign bit only, preserving
    finiteness, integer-valuedness, and the absolute-value bound. -/
axiom Float.abs_isSafeInteger {x : Float} (h : Thales.TS.isInteger x = true) :
  Thales.TS.isInteger x.abs = true

/-- Float.abs is non-negative. Postulated alongside the boundary axioms. -/
axiom Float.abs_nonneg (x : Float) : x.abs ≥ 0.0

namespace Math
  /-- Overload of `Math.abs` for refinement-typed `Integer` argument: the
      absolute value of a safe integer is a non-negative safe integer
      (`Natural`). Both halves of `isNatural` come from postulated boundary
      axioms (`Float.abs_isInteger`, `Float.abs_nonneg`). -/
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
