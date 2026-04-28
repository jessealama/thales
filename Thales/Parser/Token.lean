/-
  Thales/Parser/Token.lean
  Token definitions for the native JavaScript parser
-/
import Thales.AST

namespace Thales.Parser

open Thales.AST

/-- Token kinds for JavaScript lexer -/
inductive TokenKind where
  -- Literals
  | number (value : Float)
  | bigint (value : Int)
  | string (value : String)
  | regex (pattern : String) (flags : String)  -- /pattern/flags
  -- Template literals
  | templateHead (value : String) (rawValue : String)     -- `hello ${
  | templateMiddle (value : String) (rawValue : String)   -- } world ${
  | templateTail (value : String) (rawValue : String)     -- } end`
  | templateNoSub (value : String) (rawValue : String)    -- `no interpolation`
  | «true»
  | «false»
  | null

  -- Identifiers and keywords
  | identifier (name : String)
  | privateIdentifier (name : String)  -- #identifier (name excludes the #)

  -- Keywords
  | «var»
  | «let»
  | «const»
  | «function»
  | «return»
  | «if»
  | «else»
  | «while»
  | «do»
  | «for»
  | «break»
  | «continue»
  | «switch»
  | «case»
  | «default»
  | «throw»
  | «try»
  | «catch»
  | «finally»
  | «new»
  | «this»
  | «typeof»
  | «void»
  | «delete»
  | «in»
  | «instanceof»
  | «class»
  | «extends»
  | «super»
  | «static»
  | «get»
  | «set»
  | «async»
  | «await»
  | «yield»
  | «of»
  | «with»
  | «debugger»

  -- TypeScript keywords (only emitted in TS mode)
  | «interface»
  | «type»
  | enum_
  | as_
  | is_
  | keyof
  | «readonly»
  | implements_
  | «declare»
  | satisfies
  | «infer»

  -- Punctuation
  | lparen      -- (
  | rparen      -- )
  | lbrace      -- {
  | rbrace      -- }
  | lbracket    -- [
  | rbracket    -- ]
  | semicolon   -- ;
  | comma       -- ,
  | dot         -- .
  | colon       -- :
  | question    -- ?
  | arrow       -- =>
  | ellipsis    -- ...

  -- Operators
  | plus        -- +
  | minus       -- -
  | star        -- *
  | starstar    -- **
  | slash       -- /
  | percent     -- %
  | plusplus    -- ++
  | minusminus  -- --

  -- Comparison
  | lt          -- <
  | gt          -- >
  | leq         -- <=
  | geq         -- >=
  | eq          -- ==
  | neq         -- !=
  | seq         -- ===
  | sneq        -- !==

  -- Bitwise
  | amp         -- &
  | pipe        -- |
  | caret       -- ^
  | tilde       -- ~
  | ltlt        -- <<
  | gtgt        -- >>
  | gtgtgt      -- >>>

  -- Logical
  | ampamp      -- &&
  | pipepipe    -- ||
  | bang        -- !
  | questionquestion  -- ??

  -- Assignment
  | assign      -- =
  | pluseq      -- +=
  | minuseq     -- -=
  | stareq      -- *=
  | slasheq     -- /=
  | percenteq   -- %=
  | starstareq  -- **=
  | ltlteq      -- <<=
  | gtgteq      -- >>=
  | gtgtgteq    -- >>>=
  | ampeq       -- &=
  | pipeeq      -- |=
  | careteq     -- ^=
  | ampampeq    -- &&=
  | pipepipeeq  -- ||=
  | questionquestioneq  -- ??=

  -- Optional chaining
  | questiondot  -- ?.

  -- Special
  | eof
  deriving Repr, Inhabited, BEq

/-- A token with position information -/
structure Token where
  kind : TokenKind
  raw : String  -- Original source text of the token
  pos : Position  -- Start position
  endPos : Position  -- End position
  deriving Repr, Inhabited

/-- Check if a string is a reserved keyword and return its token kind -/
def stringToKeyword (s : String) : Option TokenKind :=
  match s with
  | "var" => some .var
  | "let" => some .let
  | "const" => some .const
  | "function" => some .function
  | "return" => some .return
  | "if" => some .if
  | "else" => some .else
  | "while" => some .while
  | "do" => some .do
  | "for" => some .for
  | "break" => some .break
  | "continue" => some .continue
  | "switch" => some .switch
  | "case" => some .case
  | "default" => some .default
  | "throw" => some .throw
  | "try" => some .try
  | "catch" => some .catch
  | "finally" => some .finally
  | "new" => some .new
  | "this" => some .this
  | "typeof" => some .typeof
  | "void" => some .void
  | "delete" => some .delete
  | "in" => some .in
  | "instanceof" => some .instanceof
  | "class" => some .class
  | "extends" => some .extends
  | "super" => some .super
  | "static" => some .static
  | "get" => some .get
  | "set" => some .set
  | "async" => some .async
  | "await" => some .await
  | "yield" => some .yield
  | "of" => some .of
  | "with" => some .with
  | "debugger" => some .debugger
  | "true" => some .true
  | "false" => some .false
  | "null" => some .null
  | "interface" => some .interface
  | "type" => some .type
  | "enum" => some .enum_
  | "as" => some .as_
  | "is" => some .is_
  | "keyof" => some .keyof
  | "readonly" => some .readonly
  | "implements" => some .implements_
  | "declare" => some .declare
  | "satisfies" => some .satisfies
  | "infer" => some .infer
  | _ => none

/-- Convert binary operator token to AST operator -/
def tokenToBinaryOp : TokenKind → Option BinaryOperator
  | .eq => some .eq
  | .neq => some .neq
  | .seq => some .seq
  | .sneq => some .sneq
  | .lt => some .lt
  | .leq => some .leq
  | .gt => some .gt
  | .geq => some .geq
  | .ltlt => some .shl
  | .gtgt => some .shr
  | .gtgtgt => some .ushr
  | .plus => some .add
  | .minus => some .sub
  | .star => some .mul
  | .slash => some .div
  | .percent => some .mod
  | .starstar => some .exp
  | .pipe => some .bitor
  | .caret => some .bitxor
  | .amp => some .bitand
  | .in => some .in
  | .instanceof => some .instanceof
  | _ => none

/-- Convert logical operator token to AST operator -/
def tokenToLogicalOp : TokenKind → Option LogicalOperator
  | .ampamp => some .and
  | .pipepipe => some .or
  | .questionquestion => some .nullishCoalesce
  | _ => none

/-- Convert unary operator token to AST operator -/
def tokenToUnaryOp : TokenKind → Option UnaryOperator
  | .minus => some .neg
  | .plus => some .pos
  | .bang => some .not
  | .tilde => some .bitnot
  | .typeof => some .typeof
  | .void => some .void
  | .delete => some .delete
  | _ => none

/-- Convert update operator token to AST operator -/
def tokenToUpdateOp : TokenKind → Option UpdateOperator
  | .plusplus => some .inc
  | .minusminus => some .dec
  | _ => none

/-- Convert assignment operator token to AST operator -/
def tokenToAssignOp : TokenKind → Option AssignmentOperator
  | .assign => some .assign
  | .pluseq => some .addAssign
  | .minuseq => some .subAssign
  | .stareq => some .mulAssign
  | .slasheq => some .divAssign
  | .percenteq => some .modAssign
  | .starstareq => some .expAssign
  | .ltlteq => some .shlAssign
  | .gtgteq => some .shrAssign
  | .gtgtgteq => some .ushrAssign
  | .pipeeq => some .orAssign
  | .careteq => some .xorAssign
  | .ampeq => some .andAssign
  | .pipepipeeq => some .orLogicalAssign
  | .ampampeq => some .andLogicalAssign
  | .questionquestioneq => some .nullishAssign
  | _ => none

/-- Check if a token kind is an assignment operator -/
def isAssignmentOp : TokenKind → Bool
  | .assign | .pluseq | .minuseq | .stareq | .slasheq | .percenteq
  | .starstareq | .ltlteq | .gtgteq | .gtgtgteq | .pipeeq | .careteq
  | .ampeq | .pipepipeeq | .ampampeq | .questionquestioneq => true
  | _ => false

/-- Get precedence for binary/logical operators (higher = tighter binding)
    Returns 0 for non-operators -/
def getOperatorPrecedence : TokenKind → Nat
  -- Comma (sequence)
  | .comma => 1
  -- Assignment operators (right-to-left)
  | .assign | .pluseq | .minuseq | .stareq | .slasheq | .percenteq
  | .starstareq | .ltlteq | .gtgteq | .gtgtgteq | .pipeeq | .careteq
  | .ampeq | .pipepipeeq | .ampampeq | .questionquestioneq => 2
  -- Ternary conditional
  | .question => 3
  -- Nullish coalescing
  | .questionquestion => 4
  -- Logical OR
  | .pipepipe => 5
  -- Logical AND
  | .ampamp => 6
  -- Bitwise OR
  | .pipe => 7
  -- Bitwise XOR
  | .caret => 8
  -- Bitwise AND
  | .amp => 9
  -- Equality
  | .eq | .neq | .seq | .sneq => 10
  -- Relational
  | .lt | .gt | .leq | .geq | .in | .instanceof => 11
  -- Bitwise shift
  | .ltlt | .gtgt | .gtgtgt => 12
  -- Additive
  | .plus | .minus => 13
  -- Multiplicative
  | .star | .slash | .percent => 14
  -- Exponentiation (right-to-left)
  | .starstar => 15
  -- Non-operators
  | _ => 0

/-- Check if operator is right-associative -/
def isRightAssociative : TokenKind → Bool
  | .starstar => true
  | .assign | .pluseq | .minuseq | .stareq | .slasheq | .percenteq
  | .starstareq | .ltlteq | .gtgteq | .gtgtgteq | .pipeeq | .careteq
  | .ampeq | .pipepipeeq | .ampampeq | .questionquestioneq => true
  | _ => false

end Thales.Parser
