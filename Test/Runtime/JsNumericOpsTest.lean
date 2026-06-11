/-
  Test/Runtime/JsNumericOpsTest.lean
  Pins the JS-semantics numeric helpers (#32, needed by #24's compound
  assignment): ES ToInt32/ToUint32, the bitwise/shift family, and `%`.
  Every expected value below is Node's output for the same expression.
-/
import Thales.TS.Runtime

open Thales.TS

private def expectFloat (label : String) (got expected : Float) : IO Unit := do
  -- compare via bit-faithful display to catch -0 vs 0 and NaN
  unless toString got == toString expected do
    throw (IO.userError s!"{label}: got {got}, expected {expected}")

private def expectNat (label : String) (got expected : Nat) : IO Unit := do
  unless got == expected do
    throw (IO.userError s!"{label}: got {got}, expected {expected}")

private def expectInt (label : String) (got expected : Int) : IO Unit := do
  unless got == expected do
    throw (IO.userError s!"{label}: got {got}, expected {expected}")

-- ToInt32 / ToUint32 edges
def tConv : IO Unit := do
  expectInt "toInt32 NaN" (toInt32 (0.0 / 0.0)) 0
  expectInt "toInt32 Inf" (toInt32 (1.0 / 0.0)) 0
  expectInt "toInt32 5.7" (toInt32 5.7) 5
  expectInt "toInt32 -5.7" (toInt32 (-5.7)) (-5)
  expectInt "toInt32 2^32+1" (toInt32 4294967297.0) 1
  expectInt "toInt32 2^31" (toInt32 2147483648.0) (-2147483648)
  expectNat "toUint32 -1" (toUint32 (-1.0)) 4294967295
  expectNat "toUint32 -16" (toUint32 (-16.0)) 4294967280
  expectNat "toUint32 2^85" (toUint32 38685626227668133590597632.0) 0

-- Node: 1 7 6 16 -4 15 1
def tBitwise : IO Unit := do
  expectFloat "5&3" (jsBitAnd 5.0 3.0) 1.0
  expectFloat "5|3" (jsBitOr 5.0 3.0) 7.0
  expectFloat "5^3" (jsBitXor 5.0 3.0) 6.0
  expectFloat "1<<4" (jsShl 1.0 4.0) 16.0
  expectFloat "-16>>2" (jsShr (-16.0) 2.0) (-4.0)
  expectFloat "-16>>>28" (jsUShr (-16.0) 28.0) 15.0
  expectFloat "5.7&3" (jsBitAnd 5.7 3.0) 1.0
  -- shift count masks to 5 bits: 1 << 33 === 2
  expectFloat "1<<33" (jsShl 1.0 33.0) 2.0
  -- -1 >>> 0 === 4294967295
  expectFloat "-1>>>0" (jsUShr (-1.0) 0.0) 4294967295.0

-- Node: 1 -1 1.5 NaN-cases
def tMod : IO Unit := do
  expectFloat "7%3" (jsMod 7.0 3.0) 1.0
  expectFloat "-7%3" (jsMod (-7.0) 3.0) (-1.0)
  expectFloat "5.5%2" (jsMod 5.5 2.0) 1.5
  expectFloat "7%-3" (jsMod 7.0 (-3.0)) 1.0
  unless (jsMod 7.0 0.0).isNaN do throw (IO.userError "7%0 not NaN")
  unless (jsMod (1.0 / 0.0) 3.0).isNaN do throw (IO.userError "Inf%3 not NaN")
  expectFloat "7%Inf" (jsMod 7.0 (1.0 / 0.0)) 7.0

#eval tConv
#eval tBitwise
#eval tMod
