/-
  Test/Runtime/ArrayMethodsTest.lean
  Pins the Array stdlib helpers (#28): `joinJS`, `indexOfJS`, `includesFloat`,
  `includesStr`. Every expected value is Node's result for the same call.
  Note the indexOf/includes NaN divergence: `===` vs SameValueZero.
-/
import Thales.TS.Runtime

open Thales.TS

private def expectStr (label : String) (got expected : String) : IO Unit := do
  unless got == expected do
    throw (IO.userError s!"{label}: got {repr got}, expected {repr expected}")

private def expectFloat (label : String) (got expected : Float) : IO Unit := do
  unless got == expected do
    throw (IO.userError s!"{label}: got {got}, expected {expected}")

private def expectBool (label : String) (got expected : Bool) : IO Unit := do
  unless got == expected do
    throw (IO.userError s!"{label}: got {got}, expected {expected}")

private def nums : Array Float := #[3.0, 1.0, 2.0]
private def strs : Array String := #["a", "b", "c"]
private def nan : Float := 0.0 / 0.0

def tJoin : IO Unit := do
  expectStr "nums.join(\",\")" (Array.joinJS nums ",") "3,1,2"
  expectStr "nums.join(\" - \")" (Array.joinJS nums " - ") "3 - 1 - 2"
  expectStr "strs.join(\"\")" (Array.joinJS strs "") "abc"
  expectStr "strs.join(\",\")" (Array.joinJS strs ",") "a,b,c"
  expectStr "empty.join(\",\")" (Array.joinJS (#[] : Array Float) ",") ""

def tIndexOf : IO Unit := do
  expectFloat "nums.indexOf(2)" (Array.indexOfJS nums 2.0) 2.0
  expectFloat "nums.indexOf(9)" (Array.indexOfJS nums 9.0) (-1.0)
  expectFloat "strs.indexOf(b)" (Array.indexOfJS strs "b") 1.0
  expectFloat "strs.indexOf(z)" (Array.indexOfJS strs "z") (-1.0)
  -- indexOf uses ===, so NaN never matches:
  expectFloat "[NaN].indexOf(NaN)" (Array.indexOfJS #[nan] nan) (-1.0)
  -- #67: optional fromIndex (truncates toward zero, negative counts from end):
  expectFloat "nums.indexOf(2,1)" (Array.indexOfFromJS nums 2.0 1.0) 2.0
  expectFloat "nums.indexOf(3,1)" (Array.indexOfFromJS nums 3.0 1.0) (-1.0)
  expectFloat "nums.indexOf(3,-100)" (Array.indexOfFromJS nums 3.0 (-100.0)) 0.0
  expectFloat "nums.indexOf(2,5)" (Array.indexOfFromJS nums 2.0 5.0) (-1.0)
  expectFloat "nums.indexOf(2,1.9)" (Array.indexOfFromJS nums 2.0 1.9) 2.0
  expectFloat "strs.indexOf(c,1)" (Array.indexOfFromJS strs "c" 1.0) 2.0
  expectFloat "strs.indexOf(a,1)" (Array.indexOfFromJS strs "a" 1.0) (-1.0)

def tIncludes : IO Unit := do
  expectBool "nums.includes(3)" (Array.includesFloat nums 3.0) true
  expectBool "nums.includes(9)" (Array.includesFloat nums 9.0) false
  -- includes uses SameValueZero, so NaN matches NaN:
  expectBool "[NaN].includes(NaN)" (Array.includesFloat #[nan] nan) true
  expectBool "strs.includes(a)" (Array.includesStr strs "a") true
  expectBool "strs.includes(z)" (Array.includesStr strs "z") false
  -- #67: optional fromIndex:
  expectBool "nums.includes(2,1)" (Array.includesFloatFrom nums 2.0 1.0) true
  expectBool "nums.includes(3,1)" (Array.includesFloatFrom nums 3.0 1.0) false
  expectBool "nums.includes(2,5)" (Array.includesFloatFrom nums 2.0 5.0) false
  expectBool "[NaN].includes(NaN,-1)" (Array.includesFloatFrom #[nan] nan (-1.0)) true
  expectBool "strs.includes(a,1)" (Array.includesStrFrom strs "a" 1.0) false
  expectBool "strs.includes(c,-1)" (Array.includesStrFrom strs "c" (-1.0)) true

private def rep : Array Float := #[1.0, 2.0, 1.0, 2.0]
private def strs4 : Array String := #["a", "b", "c", "b"]

def tFindIndex : IO Unit := do
  expectFloat "nums.findIndex(>1)" (Array.findIndexJS nums (· > 1.0)) 0.0
  expectFloat "nums.findIndex(>5)" (Array.findIndexJS nums (· > 5.0)) (-1.0)
  expectFloat "rep.findIndex(==2)" (Array.findIndexJS rep (· == 2.0)) 1.0
  expectBool "nums.some(>1)" (nums.any (· > 1.0)) true
  expectBool "nums.every(>1)" (nums.all (· > 1.0)) false
  expectBool "nums.every(>0)" (nums.all (· > 0.0)) true

def tLastIndexOf : IO Unit := do
  expectFloat "rep.lastIndexOf(1)" (Array.lastIndexOfJS rep 1.0) 2.0
  expectFloat "rep.lastIndexOf(2)" (Array.lastIndexOfJS rep 2.0) 3.0
  expectFloat "rep.lastIndexOf(9)" (Array.lastIndexOfJS rep 9.0) (-1.0)
  expectFloat "rep.lastIndexOf(1,1)" (Array.lastIndexOfFromJS rep 1.0 1.0) 0.0
  expectFloat "rep.lastIndexOf(2,-1)" (Array.lastIndexOfFromJS rep 2.0 (-1.0)) 3.0
  expectFloat "rep.lastIndexOf(2,-3)" (Array.lastIndexOfFromJS rep 2.0 (-3.0)) 1.0
  expectFloat "rep.lastIndexOf(2,-5)" (Array.lastIndexOfFromJS rep 2.0 (-5.0)) (-1.0)
  expectFloat "strs4.lastIndexOf(b)" (Array.lastIndexOfJS strs4 "b") 3.0
  expectFloat "strs4.lastIndexOf(b,2)" (Array.lastIndexOfFromJS strs4 "b" 2.0) 1.0
  expectFloat "strs4.lastIndexOf(z)" (Array.lastIndexOfJS strs4 "z") (-1.0)
  -- empty array: no valid search window.
  expectFloat "[].lastIndexOf(1)" (Array.lastIndexOfJS (#[] : Array Float) 1.0) (-1.0)

#eval tJoin
#eval tIndexOf
#eval tIncludes
#eval tFindIndex
#eval tLastIndexOf
