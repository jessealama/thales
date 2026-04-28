import Thales.Parser.ExpectError
import Thales.Parser.Lexer

namespace Thales.Parser.ExpectError.Test

-- Well-formed strict grammar
#guard parseDirectiveContent " @thales-expect-error TH0001 " = .strict (some 1)
#guard parseDirectiveContent " @thales-expect-error " = .strict none
#guard parseDirectiveContent "  @thales-expect-error\tTH0042\t " = .strict (some 42)

-- Loose-match-but-not-strict ⇒ malformed
#guard parseDirectiveContent " @thales-expect-erorr TH0001 " = .malformed
#guard parseDirectiveContent " @thales-expect_error TH0001 " = .malformed
#guard parseDirectiveContent " @thales-expect-error th0001 " = .malformed
#guard parseDirectiveContent " @thales-expect-error TH1 " = .malformed
#guard parseDirectiveContent " @thales-expect-error TH00001 " = .malformed
#guard parseDirectiveContent " @thales-expect-error TH0001 stuff " = .malformed

-- Not a directive at all
#guard parseDirectiveContent " unrelated comment " = .notADirective
#guard parseDirectiveContent "" = .notADirective
#guard parseDirectiveContent " @some-other-thing " = .notADirective

end Thales.Parser.ExpectError.Test

namespace Thales.Parser.Lexer.Test
open Thales.Parser

private partial def lexAll (src : String) : LexerState := Id.run do
  let mut s := LexerState.init src
  repeat
    if s.atEnd then break
    match nextToken s with
    | .ok (s', _) =>
      s := s'
      if s'.atEnd then break
    | .error _ => break
  return s

-- Simple case: one directive on its own line.
#guard (lexAll "// @thales-expect-error TH0001\nlet x = 1;").directives.size = 1
#guard (lexAll "// @thales-expect-error TH0001\nlet x = 1;").directives[0]!.expectedCode = some 1
#guard (lexAll "// @thales-expect-error TH0001\nlet x = 1;").directives[0]!.directiveLine = 1
#guard (lexAll "// @thales-expect-error TH0001\nlet x = 1;").directives[0]!.appliesToLine = 2
#guard (lexAll "// @thales-expect-error TH0001\nlet x = 1;").directives[0]!.malformed = false

-- Directive-shaped text inside a string literal MUST NOT register.
#guard (lexAll "const s = \"// @thales-expect-error TH0001\";").directives.size = 0

-- Directive-shaped text inside a template literal MUST NOT register.
#guard (lexAll "const s = `// @thales-expect-error TH0001`;").directives.size = 0

-- Directive-shaped text inside a block comment MUST NOT register.
#guard (lexAll "/* // @thales-expect-error TH0001 */ let x = 1;").directives.size = 0

-- Malformed directive registers as such.
#guard (lexAll "// @thales-expect-erorr TH0001\nlet x = 1;").directives.size = 1
#guard (lexAll "// @thales-expect-erorr TH0001\nlet x = 1;").directives[0]!.malformed = true

-- Blank/comment lines between directive and code: appliesToLine skips them.
#guard (lexAll "// @thales-expect-error TH0001\n\n// filler\nlet x = 1;").directives[0]!.appliesToLine = 4

-- Directive at EOF (no following code line): appliesToLine = 0.
#guard (lexAll "// @thales-expect-error TH0001\n").directives[0]!.appliesToLine = 0

end Thales.Parser.Lexer.Test
