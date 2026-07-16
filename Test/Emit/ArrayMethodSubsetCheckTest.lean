/-
  Test/Emit/ArrayMethodSubsetCheckTest.lean
  TH0085 keys on the receiver's resolved type, not the bare method name:
  string receivers are the checker's business (TH0087), never TH0085.
-/
import Thales.Emit.SubsetCheck
import Thales.Parser.Native

open Thales.Emit
open Thales.Parser
open Thales.TypeCheck

private def expectCode (src : String) (code : Nat) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let diags := subsetCheck prog
    unless diags.any (·.thalesCode? = some code) do
      let fmt := (diags.map (·.format "")).toList
      throw (IO.userError s!"expected TH{code}, got: {fmt}")

private def expectNoCode (src : String) (code : Nat) : IO Unit := do
  match parseTSSourceNative src with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let diags := subsetCheck prog
    if diags.any (·.thalesCode? = some code) then
      let fmt := (diags.map (·.format "")).toList
      throw (IO.userError s!"did not expect TH{code}, got: {fmt}")

/- A call receiver whose declared return type is string is a string-method
   call, not an array-method call: no TH0085. -/
def testStringCallReceiverNoTH0085 : IO Unit := expectNoCode
  "function getStr(): string { return \"abc\"; }\nconst b = getStr().includes(\"a\");"
  85

/- Same for indexOf and lastIndexOf, the other shared names. -/
def testStringCallReceiverIndexOfNoTH0085 : IO Unit := expectNoCode
  "function getStr(): string { return \"abc\"; }\nconst i = getStr().indexOf(\"a\");"
  85

/- A string-literal receiver is statically a string: no TH0085. -/
def testStringLiteralReceiverNoTH0085 : IO Unit := expectNoCode
  "const b = \"abc\".includes(\"a\");"
  85

/- An exported string-returning function still resolves. -/
def testExportedStringCallReceiverNoTH0085 : IO Unit := expectNoCode
  "export function getStr(): string { return \"abc\"; }\nconst b = getStr().includes(\"a\");"
  85

/- The same call receiver inside a declared function body also resolves. -/
def testStringCallReceiverInBodyNoTH0085 : IO Unit := expectNoCode
  "function getStr(): string { return \"abc\"; }\nfunction g(): boolean { return getStr().includes(\"a\"); }"
  85

/- A string-typed identifier receiver stays out of TH0085 (existing behavior). -/
def testStringIdentReceiverNoTH0085 : IO Unit := expectNoCode
  "function f(s: string): boolean { return s.includes(\"a\"); }"
  85

/- An array-typed call receiver still cannot be lowered: TH0085 stays. -/
def testArrayCallReceiverStillTH0085 : IO Unit := expectCode
  "function getArr(): number[] { return [3, 1, 2]; }\nconst s = getArr().join(\",\");"
  85

/- An unresolvable receiver (call of an undeclared/unannotated function)
   still draws TH0085. -/
def testUnknownCallReceiverStillTH0085 : IO Unit := expectCode
  "function mystery(n) { return n; }\nconst s = mystery(1).join(\",\");"
  85

/- An unresolvable receiver's message must not assert array-hood — the
   receiver could be a string shape the subset checker cannot see. -/
def testUnresolvableReceiverMessageNeutral : IO Unit := do
  match parseTSSourceNative
      "function mystery(n) { return n; }\nconst s = mystery(1).join(\",\");" with
  | .error e => throw (IO.userError s!"parse: {e}")
  | .ok prog =>
    let msgs := ((subsetCheck prog).filter (·.thalesCode? = some 85)).map (·.format "")
    unless msgs.size > 0 do
      throw (IO.userError "expected TH0085 on an unresolvable receiver")
    if msgs.any (fun m => (m.splitOn "Array method").length > 1) then
      throw (IO.userError s!"message asserts array-hood: {msgs.toList}")

/- An identifier receiver with a non-lowerable element type still draws
   TH0085 (existing behavior). -/
def testBadElementTypeStillTH0085 : IO Unit := expectCode
  "function f(xs: boolean[]): number { return xs.indexOf(true); }"
  85

#eval testStringCallReceiverNoTH0085
#eval testStringCallReceiverIndexOfNoTH0085
#eval testStringLiteralReceiverNoTH0085
#eval testExportedStringCallReceiverNoTH0085
#eval testStringCallReceiverInBodyNoTH0085
#eval testStringIdentReceiverNoTH0085
#eval testArrayCallReceiverStillTH0085
#eval testUnknownCallReceiverStillTH0085
#eval testUnresolvableReceiverMessageNeutral
#eval testBadElementTypeStillTH0085
#eval IO.println "ArrayMethodSubsetCheckTest: OK"
