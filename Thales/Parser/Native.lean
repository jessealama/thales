/-
  Thales/Parser/Native.lean
  Native TypeScript parser entry points
-/
import Thales.Parser.Pratt

namespace Thales.Parser

open Thales.TypeCheck

/-- Parse TypeScript source code -/
def parseTSSourceNative (source : String) : Except String TSProgram :=
  parseTSSource source

/-- Parse a TypeScript file -/
def parseTSFileNative (filename : String) : IO (Except String TSProgram) := do
  let source ← IO.FS.readFile filename
  return parseTSSourceNative source

end Thales.Parser
