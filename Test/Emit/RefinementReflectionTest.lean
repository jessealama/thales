/-
  Test/Emit/RefinementReflectionTest.lean
  Bitrot tripwire for the Float-Int reflection in Thales.TS.Runtime.
  Exercises predicates, throwing constructors, the four boundary
  axioms, and the homomorphism theorems with concrete inputs so a
  missing or renamed definition fails the test. Must be free of
  unfinished proofs.

  Note: `decide` does not reduce on `Float` predicates in Lean v4.29.0
  (Float ops are opaque to the elaborator), so `native_decide` is used
  for predicate checks on concrete Float literals.
-/

import Thales.TS.Runtime

set_option autoImplicit false

open Thales.TS

-- Predicates on concrete inputs.
example : isInteger 42.0 = true := by native_decide
example : isInteger 3.14 = false := by native_decide
example : isInteger 9007199254740992.0 = false := by native_decide  -- 2^53, unsafe
example : isNatural 0.0 = true := by native_decide
example : isNatural (-1.0) = false := by native_decide
example : isByte 255.0 = true := by native_decide
example : isByte 256.0 = false := by native_decide
example : isBit 0.0 = true := by native_decide
example : isBit 1.0 = true := by native_decide
example : isBit 2.0 = false := by native_decide
example : isBit (-0.0) = true := by native_decide  -- -0 admitted as Bit

-- Subtype construction.
example : Integer := ⟨42.0, by native_decide⟩
example : Bit := ⟨0.0, by native_decide⟩
example : Bit := ⟨-0.0, by native_decide⟩

-- Coercion chain.
example (b : Bit) : Float := b
example (n : Natural) : Integer := n

-- Round-trip on a small concrete input.
example : (Integer.ofInt 42 (by decide)).toInt = 42 := by
  apply Integer.toInt_ofInt

-- The four boundary axioms — referenced by name (rename = test fails).
#check @Float.ofInt_neg
#check @Float.ofInt_lt
#check @Float.ofInt_le
#check @Float.toUInt64_of_isNatural

-- Homomorphism theorems — referenced by name.
#check @Integer.toInt_ofInt
#check @Integer.add_homomorphism
#check @Integer.sub_homomorphism
#check @Integer.mul_homomorphism

-- Throwing constructors on valid input do NOT throw at compile time.
-- The `dite` reduces via `dif_pos` once the predicate is discharged
-- by `native_decide`.
example : (asInteger 42.0).val = 42.0 := by
  unfold asInteger
  rw [dif_pos (by native_decide : isInteger 42.0 = true)]
