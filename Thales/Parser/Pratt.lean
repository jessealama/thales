import Thales.Parser.Lexer
import Thales.TypeCheck.TSAST

namespace Thales.Parser

open Thales.AST
open Thales.TypeCheck

/-- Parser state wrapping lexer state with peeked token -/
structure ParserState where
  lexer : LexerState
  current : Token
  deriving Repr

abbrev ParseResult (α : Type) := Except String α

/-- Initialize parser from source string -/
def ParserState.init (source : String) : ParseResult ParserState := do
  let lexer := LexerState.init source
  let (lexer', token) ← nextToken lexer
  return { lexer := lexer', current := token }

/-- Peek at current token -/
def ParserState.peek (p : ParserState) : Token := p.current

/-- Check if current token matches -/
def ParserState.check (p : ParserState) (kind : TokenKind) : Bool :=
  p.current.kind == kind

/-- Advance to next token -/
def ParserState.advance (p : ParserState) : ParseResult ParserState := do
  let (lexer', token) ← nextToken p.lexer
  return { lexer := lexer', current := token }

/-- Advance expecting template continuation when current token is }
    We need to re-lex from the } position to get templateMiddle/templateTail -/
def ParserState.advanceTemplate (p : ParserState) : ParseResult ParserState := do
  -- The current token is }, and p.lexer is positioned right after it.
  -- We need to go back to the } and parse as template continuation.
  -- Since } is a single character, pos - 1 should be at the }.
  let lexerAtBrace : LexerState := {
    p.lexer with
    pos := p.lexer.pos - 1
    column := p.lexer.column - 1
  }
  let (lexer', token') ← parseTemplate lexerAtBrace false
  return { lexer := lexer', current := token' }

/-- Consume a token of expected kind or error -/
def ParserState.expect (p : ParserState) (kind : TokenKind) (msg : String) : ParseResult ParserState := do
  if p.check kind then
    p.advance
  else
    throw s!"{msg} at line {p.current.pos.line}, got {repr p.current.kind}"

/-- Check if at end of input -/
def ParserState.atEnd (p : ParserState) : Bool :=
  p.current.kind == .eof

/-- Whether a token can serve as a member-access name (after `.`).
    Accepts identifiers and any keyword-shaped token (raw text starts with
    an identifier-start character). -/
def Token.isIdentName (t : Token) : Bool :=
  match t.kind with
  | .identifier _ => true
  | _ =>
    match t.raw.toList with
    | [] => false
    | c :: _ => c.isAlpha || c == '_' || c == '$'

/-- Get source location from two positions -/
def makeSourceLoc (start : Position) (endPos : Position) : Option SourceLocation :=
  some { start, «end» := endPos }

/-- Create NodeBase from positions -/
def makeBase (start : Position) (endPos : Position) : NodeBase :=
  { loc := makeSourceLoc start endPos }

/-- Get start position from expression -/
def getExprStart : Expression → Position
  | .identifier base _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .literal base _ _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .thisExpr base => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .arrayExpr base _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .objectExpr base _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .functionExpr base _ _ _ _ _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .arrowFunctionExpr base _ _ _ _ _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .unaryExpr base _ _ _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .updateExpr base _ _ _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .binaryExpr base _ _ _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .assignmentExpr base _ _ _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .logicalExpr base _ _ _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .memberExpr base _ _ _ _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .privateMemberExpr base _ _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .conditionalExpr base _ _ _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .callExpr base _ _ _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .newExpr base _ _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .chainExpr base _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .sequenceExpr base _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .templateLiteral base _ _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .taggedTemplate base _ _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .classExpr base .. => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .super_ base => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .spreadElement base _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .yieldExpr base _ _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .awaitExpr base _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .patternExpr base _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }
  | .metaProperty base _ _ => base.loc.map (·.start) |>.getD { line := 1, column := 0 }

/-- Skip a TypeScript type annotation by counting brackets.
    Used in contexts where we need to erase types but the full type parser
    isn't available (e.g., variable declarators inside function bodies).
    Stops before =, ,, ;, }, ), ] at nesting level 0. -/
partial def skipTSType (p : ParserState) (depth : Nat := 0) : ParseResult ParserState := do
  match p.current.kind with
  | .eof => return p
  | .lbracket | .lbrace | .lparen | .lt =>
    let p1 ← p.advance
    let p2 ← skipTSType p1 (depth + 1)
    skipTSType p2 depth
  | .rbracket | .rbrace | .rparen =>
    if depth == 0 then return p
    else let p1 ← p.advance; skipTSType p1 (depth - 1)
  | .gt =>
    if depth == 0 then return p
    else let p1 ← p.advance; skipTSType p1 (depth - 1)
  | .assign | .comma | .semicolon =>
    if depth == 0 then return p
    else let p1 ← p.advance; skipTSType p1 depth
  | .pipe | .amp =>
    -- Union/intersection: keep consuming at same depth
    let p1 ← p.advance; skipTSType p1 depth
  | _ =>
    let p1 ← p.advance; skipTSType p1 depth

/-- Skip a TypeScript return type annotation (between `)` and `{`).
    Like skipTSType but also stops at `{` at depth 0 (the function body opener). -/
partial def skipTSReturnType (p : ParserState) (depth : Nat := 0) : ParseResult ParserState := do
  match p.current.kind with
  | .eof => return p
  | .lbrace =>
    if depth == 0 then return p  -- stop before function body
    else let p1 ← p.advance; let p2 ← skipTSReturnType p1 (depth + 1); skipTSReturnType p2 depth
  | .lbracket | .lparen | .lt =>
    let p1 ← p.advance
    let p2 ← skipTSReturnType p1 (depth + 1)
    skipTSReturnType p2 depth
  | .rbracket | .rbrace | .rparen =>
    if depth == 0 then return p
    else let p1 ← p.advance; skipTSReturnType p1 (depth - 1)
  | .gt =>
    if depth == 0 then return p
    else let p1 ← p.advance; skipTSReturnType p1 (depth - 1)
  | .assign | .comma | .semicolon =>
    if depth == 0 then return p
    else let p1 ← p.advance; skipTSReturnType p1 depth
  | .pipe | .amp =>
    let p1 ← p.advance; skipTSReturnType p1 depth
  | _ =>
    let p1 ← p.advance; skipTSReturnType p1 depth

/-- Skip a TS postfix expression operator: as T, satisfies T, ! -/
partial def skipTSExprPostfix (p : ParserState) : ParseResult ParserState := do
  match p.current.kind with
  | .as_ =>
    let p1 ← p.advance
    let p2 ← skipTSType p1
    skipTSExprPostfix p2
  | .satisfies =>
    let p1 ← p.advance
    let p2 ← skipTSType p1
    skipTSExprPostfix p2
  | .bang =>
    let p1 ← p.advance
    skipTSExprPostfix p1
  | _ => return p

/-- Inner loop for trySkipGenericArgs: walk tokens inside <...> with depth tracking.
    Returns Some state positioned after the closing > on success, None on failure. -/
private partial def skipGenericArgsLoop (ps : ParserState) (depth : Nat) (fuel : Nat) : Option ParserState :=
  if fuel == 0 then none
  else match ps.current.kind with
  | .eof | .semicolon | .lbrace | .rbrace => none
  | .lt =>
    match ps.advance with
    | .error _ => none
    | .ok pp => skipGenericArgsLoop pp (depth + 1) (fuel - 1)
  | .gt =>
    if depth == 1 then
      match ps.advance with
      | .error _ => none
      | .ok pp => some pp
    else
      match ps.advance with
      | .error _ => none
      | .ok pp => skipGenericArgsLoop pp (depth - 1) (fuel - 1)
  | .gtgt =>
    if depth == 1 then
      -- >> but we only need one >; synthesize a remaining > token
      let tok := ps.current
      some { ps with current := {
        kind := .gt, raw := ">"
        pos := { line := tok.pos.line, column := tok.pos.column + 1 }
        endPos := tok.endPos
      } }
    else if depth == 2 then
      match ps.advance with
      | .error _ => none
      | .ok pp => some pp
    else
      match ps.advance with
      | .error _ => none
      | .ok pp => skipGenericArgsLoop pp (depth - 2) (fuel - 1)
  | _ =>
    match ps.advance with
    | .error _ => none
    | .ok pp => skipGenericArgsLoop pp depth (fuel - 1)

/-- Try to skip generic type arguments <...> in expression position.
    Returns Some with state positioned after the closing > if the <...>
    looks like type arguments (balanced angle brackets with valid content).
    Returns None if it doesn't look like type args, so the caller can
    fall back to treating < as a comparison operator. -/
private def trySkipGenericArgs (p : ParserState) : Option ParserState :=
  if p.current.kind != .lt then none
  else
    match p.advance with
    | .error _ => none
    | .ok p1 => skipGenericArgsLoop p1 1 100

/-- Skip a TS type annotation using iterative balanced bracket counting.
    Unlike skipTSType, this correctly handles nested brackets like { [K in keyof T]: ... }.
    Stops when it reaches a statement-ending token (;, =, ,, {, ), ]) at depth 0. -/
partial def skipTSTypeBalanced (p : ParserState) : ParseResult ParserState := do
  let mut ps := p
  let mut depth : Nat := 0
  -- Skip type tokens until we find a stop token at depth 0
  while !ps.atEnd do
    match ps.current.kind with
    | .semicolon | .assign | .comma =>
      if depth == 0 then return ps
      else ps ← ps.advance
    | .lbrace | .lbracket | .lparen | .lt =>
      depth := depth + 1
      ps ← ps.advance
    | .rbrace | .rbracket | .rparen =>
      if depth == 0 then return ps
      else
        depth := depth - 1
        ps ← ps.advance
    | .gt =>
      if depth == 0 then return ps
      else
        depth := depth - 1
        ps ← ps.advance
    | .eof => return ps
    | _ => ps ← ps.advance
  return ps

-- ============================================================
-- TypeScript type expression and statement parsing
-- ============================================================

/-- Expect > in type argument context, handling >> and >>> token splitting.
    When >> appears where > is expected (nested generics like Array<Box<number>>),
    split it: consume one > and leave the other as the current token. -/
private def expectGt (ps : ParserState) : ParseResult ParserState := do
  if ps.check .gt then
    ps.advance
  else if ps.check .gtgt then
    -- >> is > > in type context. Replace current token with single >.
    -- Lexer is already past >>; next advance reads correctly from that position.
    let tok := ps.current
    return { ps with current := {
      kind := .gt, raw := ">"
      pos := { line := tok.pos.line, column := tok.pos.column + 1 }
      endPos := tok.endPos
    } }
  else if ps.check .gtgtgt then
    -- >>> is > >> in type context. Replace current token with >>.
    let tok := ps.current
    return { ps with current := {
      kind := .gtgt, raw := ">>"
      pos := { line := tok.pos.line, column := tok.pos.column + 1 }
      endPos := tok.endPos
    } }
  else
    throw s!"Expected '>' at line {ps.current.pos.line}"

mutual

/-- Parse function type parameters: (name: Type, name?: Type, ...name: Type) -/
partial def parseFunctionTypeParams (p : ParserState) : ParseResult (ParserState × List TSParamType) := do
  let mut ps := p
  let mut params : List TSParamType := []
  while !ps.check .rparen do
    if !params.isEmpty then
      ps ← ps.expect .comma "Expected ',' between type parameters"
    -- Check for rest parameter
    let isRest := ps.check .ellipsis
    if isRest then
      ps ← ps.advance
    let name ← match ps.current.kind with
      | .identifier n => pure n
      | _ => throw s!"Expected parameter name in function type at line {ps.current.pos.line}"
    ps ← ps.advance
    -- Check for optional marker
    let isOptional := ps.check .question
    if isOptional then
      ps := match ps.advance with | .ok pp => pp | .error _ => ps
    ps ← ps.expect .colon "Expected ':' after parameter name in function type"
    let (ps', ty) ← parseTypeExpression ps
    ps := ps'
    params := params ++ [.mk name ty isOptional isRest]
  return (ps, params)

/-- Parse a tuple type: [Type, Type, ...] -/
partial def parseTupleType (p : ParserState) : ParseResult (ParserState × TSType) := do
  let p1 ← p.advance  -- skip '['
  let mut ps := p1
  let mut elems : List TSType := []
  while !ps.check .rbracket do
    if !elems.isEmpty then
      ps ← ps.expect .comma "Expected ',' between tuple elements"
    let (ps', ty) ← parseTypeExpression ps
    ps := ps'
    elems := elems ++ [ty]
  ps ← ps.expect .rbracket "Expected ']' after tuple elements"
  return (ps, .tuple elems)

/-- Parse an object literal type: { name: Type } or mapped type { [K in C]: V } -/
partial def parseObjectLiteralType (p : ParserState) : ParseResult (ParserState × TSType) := do
  let p1 ← p.advance  -- skip '{'
  -- Detect mapped type: { [K in ...] or { readonly [K in ...] or { -readonly [K in ...]
  -- Peek without consuming tokens using pure lookahead
  let advancePure (s : ParserState) : ParserState :=
    match s.advance with | .ok pp => pp | .error _ => s
  let peekAfterModifiers : ParserState :=
    if p1.check .readonly then advancePure p1
    else if p1.check .minus then
      let p1' := advancePure p1
      if p1'.check .readonly then advancePure p1' else p1
    else p1
  let isMapped :=
    if peekAfterModifiers.check .lbracket then
      let afterBracket := advancePure peekAfterModifiers
      match afterBracket.current.kind with
      | .identifier _ => (advancePure afterBracket).check .in
      | _ => false
    else false
  if isMapped then
    let mut ps := p1
    -- Parse readonly modifier
    let readonlyMod ← if ps.check .readonly then
      ps := match ps.advance with | .ok pp => pp | .error _ => ps
      pure (some true)
    else if ps.check .minus then
      let ps' ← ps.advance
      if ps'.check .readonly then
        ps := match ps'.advance with | .ok pp => pp | .error _ => ps'
        pure (some false)
      else
        throw s!"Expected 'readonly' after '-' in mapped type"
    else
      pure none
    ps ← ps.expect .lbracket "Expected '[' in mapped type"
    let keyVar ← match ps.current.kind with
      | .identifier name => pure name
      | tk => throw s!"Expected key variable name in mapped type, got {repr tk}"
    ps ← ps.advance
    ps ← ps.expect .in "Expected 'in' in mapped type"
    let (ps', constraint) ← parseTypeExpression ps
    ps := ps'
    ps ← ps.expect .rbracket "Expected ']' in mapped type"
    -- Parse optional modifier: ?, -?, or nothing
    let optionalMod ← if ps.check .question then
      ps := match ps.advance with | .ok pp => pp | .error _ => ps
      pure (some true)
    else if ps.check .minus then
      let ps' ← ps.advance
      if ps'.check .question then
        ps := match ps'.advance with | .ok pp => pp | .error _ => ps'
        pure (some false)
      else
        throw s!"Expected '?' after '-' in mapped type modifier"
    else
      pure none
    ps ← ps.expect .colon "Expected ':' in mapped type"
    let (ps', valueType) ← parseTypeExpression ps
    ps := ps'
    if ps.check .semicolon then
      ps := match ps.advance with | .ok pp => pp | .error _ => ps
    ps ← ps.expect .rbrace "Expected '}' in mapped type"
    return (ps, .mapped keyVar constraint valueType optionalMod readonlyMod)
  else
    -- Regular object literal type (existing code)
    let mut ps := p1
    let mut members : List TSObjectMember := []
    while !ps.check .rbrace do
      let isReadonly := ps.check .readonly
      if isReadonly then
        ps := match ps.advance with | .ok pp => pp | .error _ => ps
      if ps.check .lbracket then
        -- Could be index signature [key: Type]: ValueType or computed property [expr]: Type
        -- Disambiguate: peek after identifier — if next is ':', it's an index signature
        let isIndexSig := match ps.advance with
          | .ok p2 =>
            match p2.current.kind with
            | .identifier _ =>
              match p2.advance with
              | .ok p3 => p3.check .colon
              | .error _ => false
            | _ => false
          | .error _ => false
        if isIndexSig then
          -- Index signature: [key: Type]: ValueType
          ps ← ps.advance  -- skip '['
          let keyName ← match ps.current.kind with
            | .identifier n => pure n
            | _ => throw s!"Expected key name in index signature at line {ps.current.pos.line}"
          ps ← ps.advance
          ps ← ps.expect .colon "Expected ':' after key name in index signature"
          let (ps', keyType) ← parseTypeExpression ps
          ps := ps'
          ps ← ps.expect .rbracket "Expected ']' in index signature"
          ps ← ps.expect .colon "Expected ':' after ']' in index signature"
          let (ps', valueType) ← parseTypeExpression ps
          ps := ps'
          members := members ++ [.indexSignature keyName keyType valueType isReadonly]
        else
          -- Computed property: [expr]: Type — skip the computed key, parse as regular property
          ps ← ps.advance  -- skip '['
          -- Skip everything until we find ']'
          while !ps.check .rbracket do
            ps ← ps.advance
          ps ← ps.advance  -- skip ']'
          -- Now parse as regular property with a placeholder name
          let isOptional := ps.check .question
          if isOptional then
            ps := match ps.advance with | .ok pp => pp | .error _ => ps
          ps ← ps.expect .colon "Expected ':' after computed property name in object type"
          let (ps', ty) ← parseTypeExpression ps
          ps := ps'
          members := members ++ [.property "__computed" ty isOptional isReadonly]
      else
        let name ← match ps.current.kind with
          | .identifier n => pure n
          | _ => throw s!"Expected member name in object type at line {ps.current.pos.line}"
        ps ← ps.advance
        let isOptional := ps.check .question
        if isOptional then
          ps := match ps.advance with | .ok pp => pp | .error _ => ps
        ps ← ps.expect .colon "Expected ':' after member name in object type"
        let (ps', ty) ← parseTypeExpression ps
        ps := ps'
        members := members ++ [.property name ty isOptional isReadonly]
      if ps.check .semicolon || ps.check .comma then
        ps := match ps.advance with | .ok pp => pp | .error _ => ps
    ps ← ps.expect .rbrace "Expected '}' in object type"
    return (ps, .object members)

/-- Parse the optional `<T, U, ...>` argument list following a type reference.
    On entry, `name` is the (possibly dotted) reference name and `p` points at
    the token immediately after it. -/
partial def parseTypeRefArgs (p : ParserState) (name : String)
    : ParseResult (ParserState × TSType) := do
  if p.check .lt then
    let p1 ← p.advance
    let mut ps := p1
    let mut args : List TSType := []
    while !ps.check .gt && !ps.check .gtgt && !ps.check .gtgtgt do
      if !args.isEmpty then
        ps ← ps.expect .comma "Expected ',' between type arguments"
      let (ps', ty) ← parseTypeExpression ps
      ps := ps'
      args := args ++ [ty]
    ps ← expectGt ps
    return (ps, .ref name args)
  else
    return (p, .ref name [])

/-- Parse a primary type: number, string, boolean, void, etc. -/
partial def parsePrimaryType (p : ParserState) : ParseResult (ParserState × TSType) := do
  match p.current.kind with
  | .keyof =>
    let p1 ← p.advance  -- skip 'keyof'
    let (p2, innerTy) ← parsePostfixType p1  -- parse the operand
    return (p2, .ref "__keyof" [innerTy])
  | .typeof =>
    -- typeof X (.Y)* — type query. Capture the qualified path so the type
    -- resolver can look it up in the variable environment.
    let mut ps ← p.advance  -- skip 'typeof'
    let mut name : String := ""
    match ps.current.kind with
    | .identifier n =>
      name := n
      ps ← ps.advance
    | _ => throw s!"Expected identifier after 'typeof' at line {ps.current.pos.line}"
    while ps.check .dot do
      let pa ← ps.advance
      if pa.current.isIdentName then
        name := name ++ "." ++ pa.current.raw
        ps ← pa.advance
      else
        throw s!"Expected identifier after '.' in typeof at line {pa.current.pos.line}"
    return (ps, .ref "__typeof" [.ref name []])
  | .this =>
    -- 'this' type — approximate as 'any' for now
    let p1 ← p.advance
    return (p1, .any)
  | .infer =>
    let p1 ← p.advance  -- skip 'infer'
    match p1.current.kind with
    | .identifier name =>
      let p2 ← p1.advance  -- skip the variable name
      -- Placeholder ID in high range to avoid collision with generic typeVars
      let placeholderId := 9000 + name.length
      return (p2, .typeVar placeholderId name none)
    | tk => throw s!"Expected identifier after 'infer', got {repr tk}"
  | .readonly =>
    -- readonly T[] or readonly Array<T> — parse as array type (ignore readonly for now)
    let p1 ← p.advance  -- skip 'readonly'
    let (p2, innerTy) ← parsePostfixType p1
    return (p2, innerTy)
  | .identifier headName =>
    let mut ps ← p.advance
    -- Accumulate dotted qualifier segments: Foo.Bar.Baz
    let mut name := headName
    while ps.check .dot do
      let pa ← ps.advance
      if pa.current.isIdentName then
        name := name ++ "." ++ pa.current.raw
        ps ← pa.advance
      else
        throw s!"Expected identifier after '.' in type reference at line {pa.current.pos.line}"
    -- Builtin keyword aliases apply only to bare (un-qualified) identifiers.
    if name == headName then
      match headName with
      | "number" => return (ps, .number)
      | "string" => return (ps, .string)
      | "boolean" => return (ps, .boolean)
      | "bigint" => return (ps, .bigint)
      | "symbol" => return (ps, .symbol)
      | "void" => return (ps, .void_)
      | "undefined" => return (ps, .undefined)
      | "null" => return (ps, .null_)
      | "never" => return (ps, .never)
      | "unknown" => return (ps, .unknown)
      | "any" => return (ps, .any)
      | _ => parseTypeRefArgs ps name
    else
      parseTypeRefArgs ps name
  | .void => let p1 ← p.advance; return (p1, .void_)
  | .null => let p1 ← p.advance; return (p1, .null_)
  | .lparen =>
    let p1 ← p.advance
    -- Heuristic: detect function type vs parenthesized type
    let isFunctionType :=
      p1.check .rparen ||  -- () => T
      p1.check .ellipsis ||  -- (...args: T) => T
      (match p1.current.kind with
       | .identifier _ =>
         match nextToken p1.lexer with
         | .ok (_, tok) => tok.kind == .colon || tok.kind == .question
         | .error _ => false
       | _ => false)
    if isFunctionType then
      let (p2, params) ← parseFunctionTypeParams p1
      let p3 ← p2.expect .rparen "Expected ')' after function type parameters"
      let p4 ← p3.expect .arrow "Expected '=>' in function type"
      let (p5, retTy) ← parseTypeExpression p4
      return (p5, .function params retTy)
    else
      let (p2, ty) ← parseTypeExpression p1
      let p3 ← p2.expect .rparen "Expected ')' after type"
      return (p3, .paren ty)
  | .lbracket => parseTupleType p
  | .lbrace => parseObjectLiteralType p
  | .string s => let p1 ← p.advance; return (p1, .stringLit s)
  | .number n => let p1 ← p.advance; return (p1, .numberLit n)
  | .true => let p1 ← p.advance; return (p1, .booleanLit true)
  | .false => let p1 ← p.advance; return (p1, .booleanLit false)
  | .minus =>
    -- Signed numeric literal in type position: `-1`, `-3.14`, etc.
    let p1 ← p.advance
    match p1.current.kind with
    | .number n =>
      let p2 ← p1.advance
      return (p2, .numberLit (-n))
    | _ => throw s!"Expected numeric literal after '-' in type at line {p1.current.pos.line}"
  | tk => throw s!"Expected type, got {repr tk} at line {p.current.pos.line}"

/-- Parse array suffix: T[], index access T["key"], or type index access T[K] -/
partial def parseArraySuffix (p : ParserState) (ty : TSType) : ParseResult (ParserState × TSType) := do
  if p.check .lbracket then
    let p1 ← p.advance  -- skip [
    if p1.check .rbracket then
      -- Array type: T[]
      let p2 ← p1.advance  -- skip ]
      parseArraySuffix p2 (.array ty)
    else
      -- Index access type: T[K], T["key"], T[keyof U], etc.
      let (p2, indexTy) ← parseTypeExpression p1
      let p3 ← p2.expect .rbracket "Expected ']' in index access type"
      parseArraySuffix p3 (.ref "__indexAccess" [ty, indexTy])
  else
    return (p, ty)

/-- Parse a type with array suffix: number[], string[][] -/
partial def parsePostfixType (p : ParserState) : ParseResult (ParserState × TSType) := do
  let (p1, ty) ← parsePrimaryType p
  parseArraySuffix p1 ty

/-- Parse an intersection type: A & B & C -/
partial def parseIntersectionType (p : ParserState) : ParseResult (ParserState × TSType) := do
  let (p1, first) ← parsePostfixType p
  let mut ps := p1
  let mut types := [first]
  while ps.check .amp do
    let ps' ← ps.advance
    let (ps'', next) ← parsePostfixType ps'
    ps := ps''
    types := types ++ [next]
  if types.length == 1 then
    return (ps, first)
  else
    return (ps, .intersection types)

/-- Parse a union type: A | B | C (without conditional check)
    Used for parsing the extends clause in conditional types -/
partial def parseUnionTypeNoConditional (p : ParserState) : ParseResult (ParserState × TSType) := do
  let (p1, first) ← parseIntersectionType p
  let mut ps := p1
  let mut types := [first]
  while ps.check .pipe do
    let ps' ← ps.advance
    let (ps'', next) ← parseIntersectionType ps'
    ps := ps''
    types := types ++ [next]
  if types.length == 1 then
    return (ps, first)
  else
    return (ps, .union types)

/-- Parse a union type: A | B | C
    Also handles conditional types: A extends B ? C : D -/
partial def parseTypeExpression (p : ParserState) : ParseResult (ParserState × TSType) := do
  let (p1, first) ← parseIntersectionType p
  let mut ps := p1
  let mut types := [first]
  while ps.check .pipe do
    let ps' ← ps.advance
    let (ps'', next) ← parseIntersectionType ps'
    ps := ps''
    types := types ++ [next]
  let checkType := if types.length == 1 then first else .union types
  -- Check for conditional type: T extends U ? A : B
  if ps.check .extends then
    let pe ← ps.advance  -- skip 'extends'
    -- Parse extends clause as union but stop before '?' (don't recurse into conditional)
    let (pe', extendsType) ← parseUnionTypeNoConditional pe
    let pq ← pe'.expect .question "Expected '?' in conditional type"
    let (pt, trueType) ← parseTypeExpression pq
    let pc ← pt.expect .colon "Expected ':' in conditional type"
    let (pf, falseType) ← parseTypeExpression pc
    return (pf, .conditional checkType extendsType trueType falseType)
  else
    return (ps, checkType)

end
mutual
/-- Parse primary expression (literals, identifiers, grouping) -/
partial def parsePrimaryExpr (p : ParserState) : ParseResult (ParserState × Expression) := do
  let token := p.peek
  let startPos := token.pos

  match token.kind with
  | .number value =>
    let p' ← p.advance
    let base := makeBase startPos token.endPos
    return (p', .literal base (.number value) token.raw)

  | .bigint value =>
    let p' ← p.advance
    let base := makeBase startPos token.endPos
    return (p', .literal base (.bigint value) token.raw)

  | .string value =>
    let p' ← p.advance
    let base := makeBase startPos token.endPos
    return (p', .literal base (.string value) token.raw)

  | .regex pattern flags =>
    let p' ← p.advance
    let base := makeBase startPos token.endPos
    return (p', .literal base (.regex pattern flags) token.raw)

  | .true =>
    let p' ← p.advance
    let base := makeBase startPos token.endPos
    return (p', .literal base (.boolean true) "true")

  | .false =>
    let p' ← p.advance
    let base := makeBase startPos token.endPos
    return (p', .literal base (.boolean false) "false")

  | .null =>
    let p' ← p.advance
    let base := makeBase startPos token.endPos
    return (p', .literal base .null "null")

  | .identifier name =>
    let p' ← p.advance
    -- Check for arrow function: x => ...
    if p'.check .arrow then
      let p'' ← p'.advance
      let id : Identifier := { base := makeBase startPos token.endPos, name }
      let param := FunctionParam.simple id
      parseArrowBody p'' startPos [param]
    else
      let base := makeBase startPos token.endPos
      return (p', .identifier base name)

  | .this =>
    let p' ← p.advance
    let base := makeBase startPos token.endPos
    return (p', .thisExpr base)

  | .super =>
    let p' ← p.advance
    let base := makeBase startPos token.endPos
    return (p', .super_ base)

  | .templateNoSub value raw =>
    -- Simple template with no interpolations
    let p' ← p.advance
    let base := makeBase startPos token.endPos
    let element := TemplateElement.mk value raw true
    return (p', .templateLiteral base [element] [])

  | .templateHead value raw =>
    -- Template with interpolations: `...${expr}...`
    parseTemplateLiteral p startPos value raw

  | .lparen =>
    -- Could be: grouping expression, arrow function, or sequence expression
    parseParenExpr p startPos

  | .lbracket =>
    -- Array literal
    parseArrayLiteral p

  | .lbrace =>
    -- Object literal
    parseObjectLiteral p

  | .function =>
    parseFunctionExpr p

  | .async =>
    -- async function expression or async arrow function
    parseAsyncExpr p

  | .class =>
    parseClassExpr p

  | .new =>
    parseNewExpr p

  | _ =>
    throw s!"Unexpected token in expression: {repr token.kind} at line {token.pos.line}"

/-- Parse template literal with interpolations -/
partial def parseTemplateLiteral (p : ParserState) (startPos : Position) (firstValue : String) (firstRaw : String)
    : ParseResult (ParserState × Expression) := do
  let p' ← p.advance  -- Skip templateHead
  let firstElem := TemplateElement.mk firstValue firstRaw false
  parseTemplateRest p' startPos [firstElem] []
where
  parseTemplateRest (p : ParserState) (startPos : Position)
      (quasis : List TemplateElement) (exprs : List Expression)
      : ParseResult (ParserState × Expression) := do
    -- Parse the expression inside ${}
    let (p', expr) ← parseExpression p 0
    -- After expression, we expect } then more template content
    -- The lexer returns rbrace, but we need to re-lex as template continuation
    if !p'.check .rbrace then
      throw s!"Expected '}}' after template expression, got {repr p'.peek.kind}"
    -- Re-lex from the } to get templateMiddle or templateTail
    let p'' ← p'.advanceTemplate
    let token := p''.peek
    match token.kind with
    | .templateMiddle value raw =>
      let p''' ← p''.advance
      let elem := TemplateElement.mk value raw false
      parseTemplateRest p''' startPos (elem :: quasis) (expr :: exprs)
    | .templateTail value raw =>
      let p''' ← p''.advance
      let elem := TemplateElement.mk value raw true
      let base := makeBase startPos p'''.peek.pos
      return (p''', .templateLiteral base (quasis.reverse ++ [elem]) (expr :: exprs).reverse)
    | _ =>
      throw s!"Expected template continuation, got {repr token.kind}"

/-- Parse arrow function body after => -/
partial def parseArrowBody (p : ParserState) (startPos : Position) (params : List FunctionParam)
    (returnType : Option TypeAnnotation := none)
    : ParseResult (ParserState × Expression) := do
  if p.check .lbrace then
    -- Block body: (x) => { return x; }
    let (p', body) ← parseBlockStmt p
    let base := makeBase startPos p'.peek.pos
    return (p', .arrowFunctionExpr base params (.inr body) false false returnType)
  else
    -- Expression body: (x) => x + 1
    let (p', expr) ← parseAssignmentExpr p
    let base := makeBase startPos p'.peek.pos
    return (p', .arrowFunctionExpr base params (.inl expr) true false returnType)

/-- Convert expression to pattern (for destructuring) -/
partial def exprToPattern (expr : Expression) : ParseResult Pattern := do
  match expr with
  | .identifier base name =>
    let id : Identifier := { base, name }
    return Pattern.identifier id
  | .arrayExpr base elements =>
    let patElements ← elements.mapM fun eOpt => do
      match eOpt with
      | none => return none
      | some (.spreadElement _ arg) =>
        let pat ← exprToPattern arg
        return some (Pattern.restElement base pat)
      | some e =>
        let pat ← exprToPattern e
        return some pat
    return Pattern.arrayPattern base patElements
  | .objectExpr base properties =>
    let patProps ← properties.mapM fun prop => do
      match prop with
      | .regular propBase key value _kind computed shorthand =>
        let valuePat ← exprToPattern value
        return PatternProperty.mk propBase key valuePat computed shorthand
      | .spread spreadBase arg =>
        let argPat ← exprToPattern arg
        return PatternProperty.rest spreadBase argPat
    return Pattern.objectPattern base patProps
  | .assignmentExpr base .assign left right =>
    let leftPat ← exprToPattern left
    return Pattern.assignmentPattern base leftPat right
  | .memberExpr base obj prop computed _ =>
    return Pattern.memberPattern base obj prop computed
  | .spreadElement base arg =>
    let pat ← exprToPattern arg
    return Pattern.restElement base pat
  | _ => throw s!"Invalid destructuring pattern"

/-- Convert expression to function parameter -/
partial def exprToParam (expr : Expression) : ParseResult FunctionParam := do
  match expr with
  | .identifier base name =>
    let id : Identifier := { base, name }
    return FunctionParam.simple id
  | .assignmentExpr _ .assign left right =>
    -- Default parameter: x = 5 or [a, b] = [1, 2]
    match left with
    | .identifier base name =>
      let id : Identifier := { base, name }
      return FunctionParam.withDefault id right
    | .arrayExpr _ _ | .objectExpr _ _ =>
      -- Destructuring with default
      let pat ← exprToPattern left
      return FunctionParam.pattern (Pattern.assignmentPattern {} pat right)
    | _ => throw "Invalid default parameter"
  | .arrayExpr _ _ | .objectExpr _ _ =>
    -- Destructuring pattern parameter
    let pat ← exprToPattern expr
    return FunctionParam.pattern pat
  | _ => throw s!"Invalid arrow function parameter: expected identifier or pattern"

/-- Convert list of expressions to function parameters -/
partial def exprsToParams (exprs : List Expression) : ParseResult (List FunctionParam) := do
  exprs.mapM exprToParam

/-- Parse comma-separated list of expressions (for arrow params / sequence)
    Returns (state, expressions, optional rest pattern) -/
partial def parseParenCommaList (p : ParserState) (acc : List Expression)
    : ParseResult (ParserState × List Expression × Option Pattern) := do
  if !p.check .comma then
    return (p, acc.reverse, none)
  let p' ← p.advance
  if p'.check .rparen then
    return (p', acc.reverse, none)  -- Trailing comma
  if p'.check .ellipsis then
    -- Rest parameter: must be last
    let p'' ← p'.advance
    let token := p''.peek
    match token.kind with
    | .identifier name =>
      let p''' ← p''.advance
      let id : Identifier := { base := makeBase token.pos token.endPos, name }
      return (p''', acc.reverse, some (Pattern.identifier id))
    | .lbracket =>
      -- Rest with array destructuring: (...[a, b]) => ...
      let (p''', arrExpr) ← parseArrayLiteral p''
      let pattern ← exprToPattern arrExpr
      return (p''', acc.reverse, some pattern)
    | .lbrace =>
      -- Rest with object destructuring: (...{a, b}) => ...
      let (p''', objExpr) ← parseObjectLiteral p''
      let pattern ← exprToPattern objExpr
      return (p''', acc.reverse, some pattern)
    | _ => throw "Expected identifier or pattern after '...'"
  let (p'', expr) ← parseAssignmentExpr p'
  -- Skip optional marker and type annotation: x?: T
  let p''a := if p''.check .question then
    match p''.advance with | .ok pp => pp | .error _ => p''
  else p''
  let p'' ← if p''a.check .colon then do
    let pa ← p''a.advance
    let (pb, _) ← parseTypeExpression pa
    pure pb
  else pure p''a
  parseParenCommaList p'' (expr :: acc)

/-- Parse parenthesized expression, arrow function, or sequence -/
partial def parseParenExpr (p : ParserState) (startPos : Position)
    : ParseResult (ParserState × Expression) := do
  let p' ← p.advance  -- Skip (

  -- Empty parens: () => ... or (): T => ...
  if p'.check .rparen then
    let p'' ← p'.advance
    -- Capture optional return-type annotation so the emitter can see it.
    let (p'', retAnn) ← if p''.check .colon then do
      let pa ← p''.advance
      let (pb, ty) ← parseTypeExpression pa
      pure (pb, some ({ type := ty } : TypeAnnotation))
    else pure (p'', none)
    if p''.check .arrow then
      let p''' ← p''.advance
      return ← parseArrowBody p''' startPos [] retAnn
    else
      throw "Unexpected empty parentheses"

  -- Rest param first: (...args) => ... or (...[a, b]) => ... or (...{a, b}) => ...
  if p'.check .ellipsis then
    let p'' ← p'.advance
    let token' := p''.peek
    match token'.kind with
    | .identifier name =>
      let p''' ← p''.advance
      -- Skip optional type annotation: ...args: T[]
      let p''' ← if p'''.check .colon then do
        let pa ← p'''.advance
        let (pb, _) ← parseTypeExpression pa
        pure pb
      else pure p'''
      let p'''' ← p'''.expect .rparen "Expected ')' after rest parameter"
      -- Capture optional return-type annotation: (...args): T =>
      let (p'''', retAnn) ← if p''''.check .colon then do
        let pa ← p''''.advance
        let (pb, ty) ← parseTypeExpression pa
        pure (pb, some ({ type := ty } : TypeAnnotation))
      else pure (p'''', none)
      if p''''.check .arrow then
        let p5 ← p''''.advance
        let id : Identifier := { base := makeBase token'.pos token'.endPos, name }
        let param := FunctionParam.rest id
        return ← parseArrowBody p5 startPos [param] retAnn
      else
        throw "Expected '=>' after arrow function parameters"
    | .lbracket =>
      -- Rest with array destructuring: (...[a, b]) => ...
      let (p''', arrExpr) ← parseArrayLiteral p''
      let pattern ← exprToPattern arrExpr
      let p'''' ← p'''.expect .rparen "Expected ')' after rest parameter"
      let (p'''', retAnn) ← if p''''.check .colon then do
        let pa ← p''''.advance
        let (pb, ty) ← parseTypeExpression pa
        pure (pb, some ({ type := ty } : TypeAnnotation))
      else pure (p'''', none)
      if p''''.check .arrow then
        let p5 ← p''''.advance
        let param := FunctionParam.pattern (Pattern.restElement {} pattern)
        return ← parseArrowBody p5 startPos [param] retAnn
      else
        throw "Expected '=>' after arrow function parameters"
    | .lbrace =>
      -- Rest with object destructuring: (...{a, b}) => ...
      let (p''', objExpr) ← parseObjectLiteral p''
      let pattern ← exprToPattern objExpr
      let p'''' ← p'''.expect .rparen "Expected ')' after rest parameter"
      let (p'''', retAnn) ← if p''''.check .colon then do
        let pa ← p''''.advance
        let (pb, ty) ← parseTypeExpression pa
        pure (pb, some ({ type := ty } : TypeAnnotation))
      else pure (p'''', none)
      if p''''.check .arrow then
        let p5 ← p''''.advance
        let param := FunctionParam.pattern (Pattern.restElement {} pattern)
        return ← parseArrowBody p5 startPos [param] retAnn
      else
        throw "Expected '=>' after arrow function parameters"
    | _ => throw "Expected identifier or pattern after '...'"

  -- Parse first expression
  let (p'', expr) ← parseAssignmentExpr p'

  -- Skip optional marker and type annotation on the first param: x?: T
  let p''a := if p''.check .question then
    match p''.advance with | .ok pp => pp | .error _ => p''
  else p''
  let p'' ← if p''a.check .colon then do
    let pa ← p''a.advance
    let (pb, _) ← parseTypeExpression pa
    pure pb
  else pure p''a

  if p''.check .comma then
    -- Multiple items - could be sequence or multiple arrow params
    let (p''', exprs, restOpt) ← parseParenCommaList p'' [expr]
    let p'''' ← p'''.expect .rparen "Expected ')'"
    -- Capture optional return-type annotation: (a, b): T =>
    let (p'''', retAnn) ← if p''''.check .colon then do
      let pa ← p''''.advance
      let (pb, ty) ← parseTypeExpression pa
      pure (pb, some ({ type := ty } : TypeAnnotation))
    else pure (p'''', none)
    if p''''.check .arrow then
      -- Arrow function with multiple params
      let params ← exprsToParams exprs  -- exprs already includes expr
      let allParams := match restOpt with
        | some pat => params ++ [FunctionParam.pattern (Pattern.restElement {} pat)]
        | none => params
      let p5 ← p''''.advance
      return ← parseArrowBody p5 startPos allParams retAnn
    else
      if restOpt.isSome then
        throw "Rest element not allowed in sequence expression"
      -- Sequence expression
      let base := makeBase startPos p''''.peek.pos
      return (p'''', .sequenceExpr base exprs)
  else
    let p''' ← p''.expect .rparen "Expected ')'"
    -- Capture optional return-type annotation: (x): T =>
    let (p''', retAnn) ← if p'''.check .colon then do
      let pa ← p'''.advance
      let (pb, ty) ← parseTypeExpression pa
      pure (pb, some ({ type := ty } : TypeAnnotation))
    else pure (p''', none)
    if p'''.check .arrow then
      -- Single-param arrow function: (x) => ...
      let params ← exprsToParams [expr]
      let p'''' ← p'''.advance
      return ← parseArrowBody p'''' startPos params retAnn
    else
      -- Regular grouping
      return (p''', expr)

/-- Parse array literal [a, b, c] -/
partial def parseArrayLiteral (p : ParserState) : ParseResult (ParserState × Expression) := do
  let startPos := p.peek.pos
  let p' ← p.expect .lbracket "Expected '['"

  let (p'', elements) ← parseArrayElements p' []

  let p''' ← p''.expect .rbracket "Expected ']'"
  let base := makeBase startPos p'''.current.pos
  return (p''', .arrayExpr base elements)
where
  parseArrayElements (p : ParserState) (acc : List (Option Expression)) : ParseResult (ParserState × List (Option Expression)) := do
    if p.check .rbracket then
      return (p, acc.reverse)
    else if p.check .comma then
      -- Elision (hole in array)
      let p' ← p.advance
      parseArrayElements p' (none :: acc)
    else if p.check .ellipsis then
      -- Spread element or rest element: [...arr] or [...x]
      let startPos := p.peek.pos
      let p' ← p.advance
      let (p'', arg) ← parseAssignmentExpr p'
      let base := makeBase startPos p''.peek.pos
      let spread := Expression.spreadElement base arg
      if p''.check .comma then
        let p''' ← p''.advance
        parseArrayElements p''' (some spread :: acc)
      else
        return (p'', (some spread :: acc).reverse)
    else
      let (p', expr) ← parseAssignmentExpr p
      if p'.check .comma then
        let p'' ← p'.advance
        parseArrayElements p'' (some expr :: acc)
      else
        return (p', (some expr :: acc).reverse)

/-- Parse object literal { a: 1, b: 2 } -/
partial def parseObjectLiteral (p : ParserState) : ParseResult (ParserState × Expression) := do
  let startPos := p.peek.pos
  let p' ← p.expect .lbrace "Expected '{'"

  let (p'', properties) ← parseObjectProperties p' []

  let p''' ← p''.expect .rbrace "Expected '}'"
  let base := makeBase startPos p'''.current.pos
  return (p''', .objectExpr base properties)
where
  -- Check if this is a getter/setter: get/set followed by a property name (not : or ,)
  isGetterOrSetter (p : ParserState) : Bool :=
    match p.peek.kind with
    | .get | .set =>
      -- Look ahead: if followed by identifier, [, string, or number, it's a getter/setter
      -- if followed by :, ,, (, or } it's a regular property named "get" or "set"
      match p.lexer.input.toList.getD (p.lexer.pos) '\x00' with
      | ':' | ',' | '(' | '}' => false
      | _ => true  -- Likely followed by property name
    | _ => false

  -- Check if this is async method: async name() { ... } (not async: value)
  isAsyncMethod (p : ParserState) : Bool :=
    match p.peek.kind with
    | .async =>
      match p.lexer.input.toList.getD (p.lexer.pos) '\x00' with
      | ':' | ',' | '(' | '}' => false  -- async: value or async() method name
      | _ => true  -- async followed by something else = async method
    | _ => false

  parseObjectProperties (p : ParserState) (acc : List ObjectProperty) : ParseResult (ParserState × List ObjectProperty) := do
    if p.check .rbrace then
      return (p, acc.reverse)
    else
      let startPos := p.peek.pos
      -- Check for spread
      if p.check .ellipsis then
        let p' ← p.advance
        let (p'', expr) ← parseAssignmentExpr p'
        let base := makeBase startPos p''.peek.pos
        let prop := ObjectProperty.spread base expr
        if p''.check .comma then
          let p''' ← p''.advance
          parseObjectProperties p''' (prop :: acc)
        else
          return (p'', (prop :: acc).reverse)
      -- Check for async method: async name() { ... } or async *name() { ... }
      else if isAsyncMethod p then
        let p' ← p.advance  -- consume 'async'
        -- Check for generator: async *method()
        let (p'', isGenerator) := if p'.check .star then
          match p'.advance with
          | .ok p3 => (p3, true)
          | .error _ => (p', false)
        else (p', false)
        let (p''', key, computed) ← parsePropertyKey p''
        let (p'''', func) ← parseFunctionBody p''' none isGenerator true
        let base := makeBase startPos p''''.peek.pos
        let prop := ObjectProperty.regular base key func "init" computed false
        if p''''.check .comma then
          let p5 ← p''''.advance
          parseObjectProperties p5 (prop :: acc)
        else
          return (p'''', (prop :: acc).reverse)
      -- Check for generator method: *name() { ... }
      else if p.check .star then
        let p' ← p.advance
        let (p'', key, computed) ← parsePropertyKey p'
        let (p''', func) ← parseFunctionBody p'' none true false
        let base := makeBase startPos p'''.peek.pos
        let prop := ObjectProperty.regular base key func "init" computed false
        if p'''.check .comma then
          let p'''' ← p'''.advance
          parseObjectProperties p'''' (prop :: acc)
        else
          return (p''', (prop :: acc).reverse)
      -- Check for getter/setter: get name() { ... } or set name(v) { ... }
      else if isGetterOrSetter p then
        let kind := if p.check .get then "get" else "set"
        let p' ← p.advance
        let (p'', key, computed) ← parsePropertyKey p'
        let (p''', func) ← parseFunctionBody p'' none false false
        let base := makeBase startPos p'''.peek.pos
        let prop := ObjectProperty.regular base key func kind computed false
        if p'''.check .comma then
          let p'''' ← p'''.advance
          parseObjectProperties p'''' (prop :: acc)
        else
          return (p''', (prop :: acc).reverse)
      else
        -- Regular property
        let (p', key, computed) ← parsePropertyKey p
        if p'.check .colon then
          -- Regular property
          let p'' ← p'.advance
          let (p''', value) ← parseAssignmentExpr p''
          let base := makeBase startPos p'''.peek.pos
          let prop := ObjectProperty.regular base key value "init" computed false
          if p'''.check .comma then
            let p'''' ← p'''.advance
            parseObjectProperties p'''' (prop :: acc)
          else
            return (p''', (prop :: acc).reverse)
        else if p'.check .lparen then
          -- Method shorthand
          let (p'', func) ← parseFunctionBody p' none false false
          let base := makeBase startPos p''.peek.pos
          let prop := ObjectProperty.regular base key func "init" computed false
          if p''.check .comma then
            let p''' ← p''.advance
            parseObjectProperties p''' (prop :: acc)
          else
            return (p'', (prop :: acc).reverse)
        else if p'.check .assign then
          -- Shorthand property with default value: { x = 5 } is destructuring default
          -- We represent this as an assignment expression in the value
          let p'' ← p'.advance
          let (p''', defaultVal) ← parseAssignmentExpr p''
          let base := makeBase startPos p'''.peek.pos
          -- key = defaultVal -> create an assignment expression as the value
          let assignExpr := Expression.assignmentExpr base .assign key defaultVal
          let prop := ObjectProperty.regular base key assignExpr "init" computed true
          if p'''.check .comma then
            let p'''' ← p'''.advance
            parseObjectProperties p'''' (prop :: acc)
          else
            return (p''', (prop :: acc).reverse)
        else
          -- Shorthand property { x } is same as { x: x }
          let base := makeBase startPos p'.peek.pos
          let prop := ObjectProperty.regular base key key "init" computed true
          if p'.check .comma then
            let p'' ← p'.advance
            parseObjectProperties p'' (prop :: acc)
          else
            return (p', (prop :: acc).reverse)

  parsePropertyKey (p : ParserState) : ParseResult (ParserState × Expression × Bool) := do
    if p.check .lbracket then
      -- Computed property name
      let p' ← p.advance
      let (p'', expr) ← parseAssignmentExpr p'
      let p''' ← p''.expect .rbracket "Expected ']'"
      return (p''', expr, true)
    else
      -- Identifier or literal
      let token := p.peek
      match token.kind with
      | .identifier name =>
        let p' ← p.advance
        let base := makeBase token.pos token.endPos
        return (p', .identifier base name, false)
      | .string value =>
        let p' ← p.advance
        let base := makeBase token.pos token.endPos
        return (p', .literal base (.string value) token.raw, false)
      | .number value =>
        let p' ← p.advance
        let base := makeBase token.pos token.endPos
        return (p', .literal base (.number value) token.raw, false)
      | _ =>
        -- Keywords can be used as property names
        let p' ← p.advance
        let base := makeBase token.pos token.endPos
        let name := match token.kind with
          | .identifier n => n
          | _ => token.raw
        return (p', .identifier base name, false)

/-- Parse function expression -/
partial def parseFunctionExpr (p : ParserState) : ParseResult (ParserState × Expression) := do
  let startPos := p.peek.pos
  let p' ← p.expect .function "Expected 'function'"

  -- Check for generator: function*
  let (p'', isGenerator) := if p'.check .star then
    match p'.advance with
    | .ok p3 => (p3, true)
    | .error _ => (p', false)
  else (p', false)

  -- Optional name
  let (p''', idOpt) := if let .identifier name := p''.peek.kind then
    let id := { base := makeBase p''.peek.pos p''.peek.endPos, name }
    match p''.advance with
    | .ok p4 => (p4, some id)
    | .error _ => (p'', none)
  else (p'', none)

  let (p'''', func) ← parseFunctionBody p''' idOpt isGenerator false
  let base := makeBase startPos p''''.peek.pos
  match func with
  | .functionExpr _ id params body gen async =>
    return (p'''', .functionExpr base id params body gen async)
  | _ => throw "Internal error: expected function expression"

/-- Parse async function expression or async arrow function -/
partial def parseAsyncExpr (p : ParserState) : ParseResult (ParserState × Expression) := do
  let startPos := p.peek.pos
  let p' ← p.expect .async "Expected 'async'"

  -- Check for async function expression
  if p'.check .function then
    let p'' ← p'.advance
    -- Check for generator: async function*
    let (p''', isGenerator) := if p''.check .star then
      match p''.advance with
      | .ok p3 => (p3, true)
      | .error _ => (p'', false)
    else (p'', false)

    -- Optional name
    let (p'''', idOpt) := if let .identifier name := p'''.peek.kind then
      let id := { base := makeBase p'''.peek.pos p'''.peek.endPos, name }
      match p'''.advance with
      | .ok p4 => (p4, some id)
      | .error _ => (p''', none)
    else (p''', none)

    let (p5, func) ← parseFunctionBody p'''' idOpt isGenerator true
    let base := makeBase startPos p5.peek.pos
    match func with
    | .functionExpr _ id params body gen _ =>
      return (p5, .functionExpr base id params body gen true)
    | _ => throw "Internal error: expected function expression"

  -- Check for async arrow function with parentheses: async () => ... or async (x) => ...
  else if p'.check .lparen then
    parseParenExprAsync p' startPos

  -- Check for async arrow function without parentheses: async x => ...
  else if let .identifier name := p'.peek.kind then
    let token := p'.peek
    let p'' ← p'.advance
    if p''.check .arrow then
      let p''' ← p''.advance
      let id : Identifier := { base := makeBase token.pos token.endPos, name }
      let param := FunctionParam.simple id
      if p'''.check .lbrace then
        -- Block body: async x => { return x; }
        let (p'''', body) ← parseBlockStmt p'''
        let base := makeBase startPos p''''.peek.pos
        return (p'''', .arrowFunctionExpr base [param] (.inr body) false true)
      else
        -- Expression body: async x => x + 1
        let (p'''', expr) ← parseAssignmentExpr p'''
        let base := makeBase startPos p''''.peek.pos
        return (p'''', .arrowFunctionExpr base [param] (.inl expr) true true)
    else
      throw s!"Expected '=>' after async arrow function parameter"
  else
    throw s!"Expected 'function', '(', or identifier after 'async'"
where
  -- Parse parenthesized async arrow function parameters
  parseParenExprAsync (p : ParserState) (startPos : Position) : ParseResult (ParserState × Expression) := do
    let p' ← p.advance  -- Skip (

    -- Empty parens: async () => ...
    if p'.check .rparen then
      let p'' ← p'.advance
      if p''.check .arrow then
        let p''' ← p''.advance
        return ← parseAsyncArrowBody p''' startPos []
      else
        throw "Expected '=>' after async ()"

    -- Rest param first: async (...args) => ...
    if p'.check .ellipsis then
      let p'' ← p'.advance
      let token' := p''.peek
      match token'.kind with
      | .identifier name =>
        let p''' ← p''.advance
        let p'''' ← p'''.expect .rparen "Expected ')' after rest parameter"
        if p''''.check .arrow then
          let p5 ← p''''.advance
          let id : Identifier := { base := makeBase token'.pos token'.endPos, name }
          let param := FunctionParam.rest id
          return ← parseAsyncArrowBody p5 startPos [param]
        else
          throw "Expected '=>' after async arrow function parameters"
      | _ => throw "Expected identifier after '...'"

    -- Parse first expression
    let (p'', expr) ← parseAssignmentExpr p'

    if p''.check .comma then
      -- Multiple params
      let (p''', exprs, restOpt) ← parseParenCommaList p'' [expr]
      let p'''' ← p'''.expect .rparen "Expected ')'"
      if p''''.check .arrow then
        let params ← exprsToParams exprs
        let allParams := match restOpt with
          | some pat => params ++ [FunctionParam.pattern (Pattern.restElement {} pat)]
          | none => params
        let p5 ← p''''.advance
        return ← parseAsyncArrowBody p5 startPos allParams
      else
        throw "Expected '=>' after async arrow function parameters"
    else
      let p''' ← p''.expect .rparen "Expected ')'"
      if p'''.check .arrow then
        let params ← exprsToParams [expr]
        let p'''' ← p'''.advance
        return ← parseAsyncArrowBody p'''' startPos params
      else
        throw "Expected '=>' after async arrow function parameters"

  parseAsyncArrowBody (p : ParserState) (startPos : Position) (params : List FunctionParam)
      : ParseResult (ParserState × Expression) := do
    if p.check .lbrace then
      -- Block body: async (x) => { return x; }
      let (p', body) ← parseBlockStmt p
      let base := makeBase startPos p'.peek.pos
      return (p', .arrowFunctionExpr base params (.inr body) false true)
    else
      -- Expression body: async (x) => x + 1
      let (p', expr) ← parseAssignmentExpr p
      let base := makeBase startPos p'.peek.pos
      return (p', .arrowFunctionExpr base params (.inl expr) true true)

/-- Parse TS function parameters: (name: Type, name?: Type, ...name: Type) -/
partial def parseTSFunctionParams (p : ParserState) :
    ParseResult (ParserState × List (String × Option TypeAnnotation × Bool × Bool)) := do
  let p1 ← p.expect .lparen "Expected '(' before function parameters"
  let mut ps := p1
  let mut params : List (String × Option TypeAnnotation × Bool × Bool) := []
  while !ps.check .rparen do
    if !params.isEmpty then
      ps ← ps.expect .comma "Expected ',' between parameters"
      if ps.check .rparen then break  -- allow trailing comma
    -- Check for rest parameter: ...name
    let isRest := ps.check .ellipsis
    if isRest then
      ps ← ps.advance
    -- Parse parameter name or destructuring pattern
    let name ← match ps.current.kind with
      | .identifier n =>
        ps ← ps.advance
        pure n
      | .lbracket =>
        -- Skip balanced [ ... ] for array destructuring pattern
        ps ← ps.advance
        let mut depth : Nat := 1
        while depth > 0 do
          if ps.check .lbracket then depth := depth + 1
          else if ps.check .rbracket then depth := depth - 1
          ps ← ps.advance
        pure "_destructured"
      | .lbrace =>
        -- Skip balanced { ... } for object destructuring pattern
        ps ← ps.advance
        let mut depth : Nat := 1
        while depth > 0 do
          if ps.check .lbrace then depth := depth + 1
          else if ps.check .rbrace then depth := depth - 1
          ps ← ps.advance
        pure "_destructured"
      | _ => throw s!"Expected parameter name at line {ps.current.pos.line}"
    -- Check for optional parameter: name?
    let mut isOptional := false
    if !isRest && ps.check .question then
      ps := match ps.advance with | .ok pp => pp | .error _ => ps
      isOptional := true
    -- Check for type annotation: : Type
    let (ps', typeAnn) ← if ps.check .colon then
      let pa ← ps.advance
      let (pb, ty) ← parseTypeExpression pa
      pure (pb, some (TypeAnnotation.mk ty))
    else
      pure (ps, none)
    ps := ps'
    -- Check for default value: = expr (parameters with defaults are optional)
    if ps.check .assign then
      ps ← ps.advance  -- skip '='
      let (ps'', _) ← parseAssignmentExpr ps
      ps := ps''
      isOptional := true
    -- Tuple: (name, typeAnnotation, isOptional, isRest)
    params := params ++ [(name, typeAnn, isOptional, isRest)]
  ps ← ps.expect .rparen "Expected ')' after function parameters"
  return (ps, params)

/-- Parse class expression -/
partial def parseClassExpr (p : ParserState) : ParseResult (ParserState × Expression) := do
  let startPos := p.peek.pos
  let p' ← p.expect .class "Expected 'class'"

  -- Optional name
  let (p'', idOpt) := if let .identifier name := p'.peek.kind then
    let id : Identifier := { base := makeBase p'.peek.pos p'.peek.endPos, name }
    match p'.advance with
    | .ok p''' => (p''', some id)
    | .error _ => (p', none)
  else (p', none)

  -- Skip optional generic type parameters: class Foo<T, U> { ... }
  let (p'', hasTypeParams) :=
    match trySkipGenericArgs p'' with
    | some p''' => (p''', true)
    | none => (p'', false)

  -- Optional extends clause
  let (p''', superClass) := if p''.check .extends then
    match p''.advance with
    | .ok p3 =>
      match parseUnaryExpr p3 with  -- Parse the superclass expression
      | .ok (p4, expr) => (p4, some expr)
      | .error _ => (p'', none)
    | .error _ => (p'', none)
  else (p'', none)

  -- Optional implements clause: implements I, J (type refs skipped, flag retained)
  let (p3i, hasImplements) ← skipImplementsClause p'''

  -- Parse class body
  let (p'''', methods) ← parseClassBody p3i

  let base := makeBase startPos p''''.peek.pos
  return (p'''', .classExpr base idOpt superClass methods false hasTypeParams hasImplements)

/-- Skip an optional `implements I, J` clause, returning whether one was present.
    The type references are parsed and discarded; the flag drives TH0030. -/
partial def skipImplementsClause (p : ParserState) : ParseResult (ParserState × Bool) := do
  if p.check .implements_ then
    let mut ps ← p.advance
    let (ps1, _) ← parseTypeExpression ps
    ps := ps1
    while ps.check .comma do
      ps ← ps.advance
      let (ps2, _) ← parseTypeExpression ps
      ps := ps2
    return (ps, true)
  else
    return (p, false)

/-- Parse class body { ... } -/
partial def parseClassBody (p : ParserState) : ParseResult (ParserState × List ClassElement) := do
  let p' ← p.expect .lbrace "Expected '{'"
  let (p'', elements) ← parseClassElements p' []
  let p''' ← p''.expect .rbrace "Expected '}'"
  return (p''', elements)
where
  -- Check if this is a getter/setter in class context
  isGetterOrSetterClass (p : ParserState) : Bool :=
    match p.peek.kind with
    | .get | .set =>
      -- Look ahead in the raw input for what follows
      match p.lexer.input.toList.getD (p.lexer.pos) '\x00' with
      | '(' => false  -- get() or set() are method names
      | _ => true
    | _ => false

  parseClassElements (p : ParserState) (acc : List ClassElement) : ParseResult (ParserState × List ClassElement) := do
    if p.check .rbrace then
      return (p, acc.reverse)
    else if p.atEnd then
      -- Unexpected EOF - return what we have
      throw s!"Unexpected end of input in class body at line {p.peek.pos.line}"
    else if p.check .semicolon then
      -- Empty statement in class body
      let p' ← p.advance
      parseClassElements p' acc
    else
      let startPos := p.peek.pos

      -- Consume TS member modifiers (public/private/protected/abstract/override/readonly/declare),
      -- retaining readonly/accessibility/override on the member node. Enforcement
      -- of the retained modifiers is the subset check's concern.
      let isTSMemberModifier (kind : TokenKind) : Bool :=
        match kind with
        | .identifier n =>
          n == "public" || n == "private" || n == "protected" ||
          n == "abstract" || n == "override"
        | .readonly => true
        | .declare => true
        | _ => false
      let mut pMod := p
      let mut memReadonly := false
      let mut memAccessibility : Option Accessibility := none
      let mut memOverride := false
      while isTSMemberModifier pMod.current.kind do
        -- Stop if the modifier is being used as a member name
        -- (e.g. `readonly()` would be a method called "readonly").
        let isMemberName : Bool :=
          match pMod.advance with
          | .ok pNext => pNext.check .lparen
          | .error _ => false
        if isMemberName then break
        match pMod.current.kind with
        | .identifier "public" => memAccessibility := memAccessibility.orElse fun _ => some .public_
        | .identifier "private" => memAccessibility := memAccessibility.orElse fun _ => some .private_
        | .identifier "protected" => memAccessibility := memAccessibility.orElse fun _ => some .protected_
        | .identifier "override" => memOverride := true
        | .readonly => memReadonly := true
        | _ => pure ()
        pMod := match pMod.advance with | .ok pp => pp | .error _ => pMod
      let p := pMod

      -- Check for static
      let (p', isStatic) := if p.check .static then
        match p.advance with
        | .ok p'' => (p'', true)
        | .error _ => (p, false)
      else (p, false)

      -- Check for static initialization block: static { ... }
      if isStatic && p'.check .lbrace then
        let (p'', body) ← parseBlockStmt p'
        let base := makeBase startPos p''.peek.pos
        let stmts := match body with
          | .blockStmt _ stmts => stmts
          | other => [other]
        parseClassElements p'' (.staticBlock base stmts :: acc)
      else

      -- Check for async
      let (p'', isAsync) := if p'.check .async then
        -- async before method - but check it's not `async()` method name
        match p'.lexer.input.toList.getD (p'.lexer.pos) '\x00' with
        | '(' => (p', false)  -- async() is a method name
        | _ =>
          match p'.advance with
          | .ok p3 => (p3, true)
          | .error _ => (p', false)
      else (p', false)

      -- Check for generator: *method()
      let (p3, isGenerator) := if p''.check .star then
        match p''.advance with
        | .ok p4 => (p4, true)
        | .error _ => (p'', false)
      else (p'', false)

      -- Check for getter/setter
      let (p4, methodKind) :=
        if isGetterOrSetterClass p3 then
          if p3.check .get then
            match p3.advance with
            | .ok p5 => (p5, MethodKind.getter)
            | .error _ => (p3, MethodKind.method)
          else  -- .set
            match p3.advance with
            | .ok p5 => (p5, MethodKind.setter)
            | .error _ => (p3, MethodKind.method)
        else (p3, MethodKind.method)

      -- Parse property key
      let (p5, key, computed, privateName) ← parseClassPropertyKey p4

      -- A `?` after the member name marks the member optional. Consume it for
      -- both method (`foo?()`) and field (`foo?: T`) paths, retaining the flag.
      let (p5, memOptional) := if p5.check .question then
        match p5.advance with | .ok pp => (pp, true) | .error _ => (p5, false)
      else (p5, false)

      -- A method starts with `(` or, generically, with `<`.
      let isMethod := p5.check .lparen || p5.check .lt

      -- Skip optional generic type parameters on the method: foo<T>()
      let (p5, memHasTypeParams) := if isMethod && p5.check .lt then
        match trySkipGenericArgs p5 with
        | some pp => (pp, true)
        | none => (p5, false)
      else (p5, false)

      if isMethod then
        -- This is a method
        -- Check if this is constructor (constructors cannot be private)
        let finalKind := match key with
          | .identifier _ "constructor" => if !isStatic && privateName.isNone then MethodKind.constructor else methodKind
          | _ => methodKind

        -- Parse the signature retaining param/return annotations (same helper
        -- and shape as `annotatedFuncDecl`); fall back to the annotation-skipping
        -- path when the signature doesn't fit the TS param grammar.
        let sigToFuncParams (sig : List (String × Option TypeAnnotation × Bool × Bool)) : List FunctionParam :=
          sig.map fun (n, _, _, isRest) =>
            if isRest then FunctionParam.rest { name := n } else FunctionParam.simple { name := n }
        let annotated : ParseResult
            (ParserState × Expression × List (String × Option TypeAnnotation × Bool × Bool) × Option TypeAnnotation) := do
          let (pa, sigParams) ← parseTSFunctionParams p5
          let (pb, returnType) ← if pa.check .colon then do
            let pa' ← pa.advance
            let (pb', ty) ← parseTypeExpression pa'
            pure (pb', some (TypeAnnotation.mk ty))
          else pure (pa, none)
          -- A bodyless method (`;`) is valid for abstract methods, overload
          -- signatures, and ambient declarations. Emit an empty block body.
          if pb.check .semicolon then
            let pc ← pb.advance
            pure (pc, .functionExpr {} none (sigToFuncParams sigParams) (.blockStmt {} []) isGenerator isAsync, sigParams, returnType)
          else
            let (pc, body) ← parseBlockStmt pb
            pure (pc, .functionExpr {} none (sigToFuncParams sigParams) body isGenerator isAsync, sigParams, returnType)
        let (p6, func, sigParams, returnType) ← match annotated with
          | .ok r => pure r
          | .error _ => do
            let (p6, func) ← parseFunctionBody p5 none isGenerator isAsync
            pure (p6, func, [], none)
        let base := makeBase startPos p6.peek.pos
        let methodDef := MethodDefinition.mk base key func finalKind computed isStatic privateName
          memAccessibility memOverride memOptional memHasTypeParams sigParams returnType

        parseClassElements p6 (.method methodDef :: acc)
      else
        -- Field definition: consume optional `?` and parse the `: Type`
        -- annotation (retained on the node) before the initializer. Fall back
        -- to bracket-skipping (annotation dropped) if the type doesn't parse.
        let p5a := if p5.check .question then
          match p5.advance with | .ok pp => pp | .error _ => p5
        else p5
        let (p5b, fieldTypeAnn) ← if p5a.check .colon then do
          let pa ← p5a.advance
          match parseTypeExpression pa with
          | .ok (pb, ty) => pure (pb, some ty)
          | .error _ => do
            let pb ← skipTSType pa
            pure (pb, (none : Option TSType))
        else pure (p5a, none)
        let (p6, initExpr) ← if p5b.check .assign then do
          -- Field with initializer: x = expr
          let p5' ← p5b.advance
          let (p5'', expr) ← parseAssignmentExpr p5'
          pure (p5'', some expr)
        else do
          -- Field without initializer: x;
          pure (p5b, none)

        -- Consume optional semicolon
        let p7 := if p6.check .semicolon then
          match p6.advance with
          | .ok p' => p'
          | .error _ => p6
        else p6

        let base := makeBase startPos p7.peek.pos
        let fieldDef := FieldDefinition.mk base key initExpr computed isStatic privateName
          memReadonly memOptional fieldTypeAnn memAccessibility

        parseClassElements p7 (.field fieldDef :: acc)

  parseClassPropertyKey (p : ParserState) : ParseResult (ParserState × Expression × Bool × Option PrivateName) := do
    if p.check .lbracket then
      -- Computed property name
      let p' ← p.advance
      let (p'', expr) ← parseAssignmentExpr p'
      let p''' ← p''.expect .rbracket "Expected ']'"
      return (p''', expr, true, none)
    else
      -- Private identifier, regular identifier, string, or number
      let token := p.peek
      match token.kind with
      | .privateIdentifier name =>
        -- Private field/method: #name
        let p' ← p.advance
        let base := makeBase token.pos token.endPos
        let privateName : PrivateName := { base, name }
        -- Use the name as the key expression (for display/error purposes)
        return (p', .identifier base name, false, some privateName)
      | .identifier name =>
        let p' ← p.advance
        let base := makeBase token.pos token.endPos
        return (p', .identifier base name, false, none)
      | .string value =>
        let p' ← p.advance
        let base := makeBase token.pos token.endPos
        return (p', .literal base (.string value) token.raw, false, none)
      | .number value =>
        let p' ← p.advance
        let base := makeBase token.pos token.endPos
        return (p', .literal base (.number value) token.raw, false, none)
      | _ =>
        -- Keywords can be used as method names
        let p' ← p.advance
        let base := makeBase token.pos token.endPos
        let name := match token.kind with
          | .identifier n => n
          | _ => token.raw
        return (p', .identifier base name, false, none)

/-- Parse new expression -/
partial def parseNewExpr (p : ParserState) : ParseResult (ParserState × Expression) := do
  let startPos := p.peek.pos
  let p' ← p.expect .new "Expected 'new'"

  -- Check for new.target meta-property
  if p'.check .dot then
    let p'' ← p'.advance
    let targetToken := p''.peek
    if targetToken.raw == "target" then
      let p''' ← p''.advance
      let base := makeBase startPos p'''.peek.pos
      return (p''', .metaProperty base "new" "target")

  -- Parse the callee (can be member expression)
  let (p'', callee) ← parseNewTarget p'

  -- Skip generic type args before the argument list: new Foo<T>(args)
  let p'' :=
    match trySkipGenericArgs p'' with
    | some p''' => if p'''.check .lparen then p''' else p''
    | none => p''

  -- Parse optional arguments
  let (p''', args) := if p''.check .lparen then
    match parseCallArguments p'' with
    | .ok result => result
    | .error _ => (p'', [])
  else (p'', [])

  let base := makeBase startPos p'''.peek.pos
  return (p''', .newExpr base callee args)
where
  parseNewTarget (p : ParserState) : ParseResult (ParserState × Expression) := do
    -- Parse primary, then member accesses but not calls
    let (p', expr) ← parsePrimaryExpr p
    parseMemberAccesses p' expr

  parseMemberAccesses (p : ParserState) (expr : Expression) : ParseResult (ParserState × Expression) := do
    if p.check .dot then
      let p' ← p.advance
      let token := p'.peek
      match token.kind with
      | .privateIdentifier name =>
        -- Private member access: obj.#name
        let p'' ← p'.advance
        let propBase := makeBase token.pos token.endPos
        let privateName : PrivateName := { base := propBase, name }
        let base := makeBase (getExprStart expr) token.endPos
        parseMemberAccesses p'' (.privateMemberExpr base expr privateName)
      | _ =>
        let p'' ← p'.advance
        let base := makeBase (getExprStart expr) token.endPos
        -- Use resolved identifier name, not raw (which may contain unicode escapes)
        let propName := match token.kind with
          | .identifier name => name
          | _ => token.raw
        let prop := Expression.identifier (makeBase token.pos token.endPos) propName
        parseMemberAccesses p'' (.memberExpr base expr prop false)
    else if p.check .lbracket then
      let p' ← p.advance
      let (p'', prop) ← parseExpression p' 0
      let p''' ← p''.expect .rbracket "Expected ']'"
      let base := makeBase (getExprStart expr) p'''.peek.pos
      parseMemberAccesses p''' (.memberExpr base expr prop true)
    else
      return (p, expr)

/-- Parse function body (params and block) -/
partial def parseFunctionBody (p : ParserState) (id : Option Identifier) (generator : Bool) (async : Bool) : ParseResult (ParserState × Expression) := do
  let p' ← p.expect .lparen "Expected '('"
  let (p'', params) ← parseFunctionParams p' []
  let p''' ← p''.expect .rparen "Expected ')'"
  -- Skip return type annotation between `)` and `{`: ): ReturnType {
  let p''' ← if p'''.check .colon then do
    let pa ← p'''.advance
    skipTSReturnType pa
  else pure p'''
  -- A bodyless method (`;`) is valid for abstract methods, overload signatures,
  -- and ambient declarations. Emit an empty block body.
  if p'''.check .semicolon then
    let p4 ← p'''.advance
    let base : NodeBase := {}
    return (p4, .functionExpr base id params (.blockStmt {} []) generator async)
  let (p'''', body) ← parseBlockStmt p'''
  let base : NodeBase := {}
  return (p'''', .functionExpr base id params body generator async)
where
  -- Skip optional marker `?` and type annotation `: Type` after a param name.
  skipTSParamAnnotation (p : ParserState) : ParseResult ParserState := do
    let p1 := if p.check .question then
      match p.advance with | .ok pp => pp | .error _ => p
    else p
    if p1.check .colon then
      let pa ← p1.advance
      skipTSTypeBalanced pa
    else
      return p1

  parseFunctionParams (p : ParserState) (acc : List FunctionParam) : ParseResult (ParserState × List FunctionParam) := do
    if p.check .rparen then
      return (p, acc.reverse)
    else
      let token := p.peek
      match token.kind with
      | .identifier name =>
        let p' ← p.advance
        let id : Identifier := { base := makeBase token.pos token.endPos, name }
        -- Skip optional marker and type annotation before checking for default/comma.
        let p' ← skipTSParamAnnotation p'
        -- Check for default value: x = defaultVal
        if p'.check .assign then
          let p'' ← p'.advance
          let (p''', defaultExpr) ← parseAssignmentExpr p''
          let param := FunctionParam.withDefault id defaultExpr
          if p'''.check .comma then
            let p'''' ← p'''.advance
            parseFunctionParams p'''' (param :: acc)
          else
            return (p''', (param :: acc).reverse)
        else
          let param := FunctionParam.simple id
          if p'.check .comma then
            let p'' ← p'.advance
            parseFunctionParams p'' (param :: acc)
          else
            return (p', (param :: acc).reverse)
      | .ellipsis =>
        -- Rest parameter
        let p' ← p.advance
        let token' := p'.peek
        match token'.kind with
        | .identifier name =>
          let p'' ← p'.advance
          let id : Identifier := { base := makeBase token'.pos token'.endPos, name }
          -- Skip type annotation after rest param name
          let p'' ← skipTSParamAnnotation p''
          let param := FunctionParam.rest id
          return (p'', (param :: acc).reverse)
        | .lbracket =>
          -- Rest with array destructuring: function f(...[a, b]) {}
          let (p'', arrExpr) ← parseArrayLiteral p'
          let pattern ← exprToPattern arrExpr
          let param := FunctionParam.pattern (Pattern.restElement {} pattern)
          return (p'', (param :: acc).reverse)
        | .lbrace =>
          -- Rest with object destructuring: function f(...{a, b}) {}
          let (p'', objExpr) ← parseObjectLiteral p'
          let pattern ← exprToPattern objExpr
          let param := FunctionParam.pattern (Pattern.restElement {} pattern)
          return (p'', (param :: acc).reverse)
        | _ => throw "Expected identifier or pattern after '...'"
      | .lbracket =>
        -- Array destructuring parameter: function f([a, b]) {}
        let (p', arrExpr) ← parseArrayLiteral p
        let pattern ← exprToPattern arrExpr
        -- Skip type annotation after destructuring pattern
        let p' ← skipTSParamAnnotation p'
        -- Check for default value
        if p'.check .assign then
          let p'' ← p'.advance
          let (p''', defaultExpr) ← parseAssignmentExpr p''
          let param := FunctionParam.pattern (Pattern.assignmentPattern {} pattern defaultExpr)
          if p'''.check .comma then
            let p'''' ← p'''.advance
            parseFunctionParams p'''' (param :: acc)
          else
            return (p''', (param :: acc).reverse)
        else
          let param := FunctionParam.pattern pattern
          if p'.check .comma then
            let p'' ← p'.advance
            parseFunctionParams p'' (param :: acc)
          else
            return (p', (param :: acc).reverse)
      | .lbrace =>
        -- Object destructuring parameter: function f({a, b}) {}
        let (p', objExpr) ← parseObjectLiteral p
        let pattern ← exprToPattern objExpr
        -- Skip type annotation after destructuring pattern
        let p' ← skipTSParamAnnotation p'
        -- Check for default value
        if p'.check .assign then
          let p'' ← p'.advance
          let (p''', defaultExpr) ← parseAssignmentExpr p''
          let param := FunctionParam.pattern (Pattern.assignmentPattern {} pattern defaultExpr)
          if p'''.check .comma then
            let p'''' ← p'''.advance
            parseFunctionParams p'''' (param :: acc)
          else
            return (p''', (param :: acc).reverse)
        else
          let param := FunctionParam.pattern pattern
          if p'.check .comma then
            let p'' ← p'.advance
            parseFunctionParams p'' (param :: acc)
          else
            return (p', (param :: acc).reverse)
      | _ => throw s!"Expected parameter name or pattern, got {repr token.kind}"

/-- Parse block statement -/
partial def parseBlockStmt (p : ParserState) : ParseResult (ParserState × Statement) := do
  let startPos := p.peek.pos
  let p' ← p.expect .lbrace "Expected '{'"

  let (p'', stmts) ← parseBlockBody p' []

  let p''' ← p''.expect .rbrace "Expected '}'"
  let base := makeBase startPos p'''.peek.pos
  return (p''', .blockStmt base stmts)
where
  parseBlockBody (p : ParserState) (acc : List Statement) : ParseResult (ParserState × List Statement) := do
    if p.check .rbrace || p.atEnd then
      return (p, acc.reverse)
    else
      let (p', stmt) ← parseStatement p
      parseBlockBody p' (stmt :: acc)

/-- Parse unary expression -/
partial def parseUnaryExpr (p : ParserState) : ParseResult (ParserState × Expression) := do
  let token := p.peek
  let startPos := token.pos

  -- Check for yield expression
  -- NOTE: In non-strict mode outside generator functions, 'yield' can technically be an identifier,
  -- but without proper generator context tracking we always treat it as a yield expression.
  -- This is correct for generators and will cause runtime errors (not parse errors) outside generators.
  if token.kind == .yield then
    let p' ← p.advance
    -- Check for yield* (delegate)
    let (p'', isDelegate) := if p'.check .star then
      match p'.advance with
      | .ok p3 => (p3, true)
      | .error _ => (p', false)
    else (p', false)
    -- yield can be followed by an expression or nothing
    -- Check for tokens that cannot start an expression (end of yield)
    let isEndOfYield := p''.check .semicolon || p''.check .rbrace || p''.check .rparen ||
                        p''.check .rbracket || p''.check .comma || p''.check .colon ||
                        p''.atEnd
    if isEndOfYield && !isDelegate then
      let base := makeBase startPos p''.peek.pos
      return (p'', .yieldExpr base none false)
    else
      let (p''', arg) ← parseAssignmentExpr p''
      let base := makeBase startPos p'''.peek.pos
      return (p''', .yieldExpr base (some arg) isDelegate)

  -- Check for await expression
  -- NOTE: In non-strict mode outside async functions, 'await' can technically be an identifier,
  -- but without proper async context tracking we always treat it as an await expression.
  -- This is correct for async functions and will cause runtime errors outside async functions.
  if token.kind == .await then
    let p' ← p.advance
    let (p'', arg) ← parseUnaryExpr p'
    let base := makeBase startPos p''.peek.pos
    return (p'', .awaitExpr base arg)

  -- Check for prefix unary operators
  match tokenToUnaryOp token.kind with
  | some op =>
    let p' ← p.advance
    let (p'', arg) ← parseUnaryExpr p'
    let base := makeBase startPos p''.peek.pos
    return (p'', .unaryExpr base op true arg)
  | none =>
    -- Check for prefix update operators
    match tokenToUpdateOp token.kind with
    | some op =>
      let p' ← p.advance
      let (p'', arg) ← parseUnaryExpr p'
      let base := makeBase startPos p''.peek.pos
      return (p'', .updateExpr base op arg true)
    | none =>
      -- Parse postfix expression
      parsePostfixExpr p

/-- Parse postfix operations (call, member access, postfix operators) -/
partial def parsePostfixOps (p : ParserState) (expr : Expression) : ParseResult (ParserState × Expression) := do
    let token := p.peek
    match token.kind with
    | .lparen =>
      -- Call expression
      let (p', args) ← parseCallArguments p
      let base := makeBase (getExprStart expr) p'.peek.pos
      parsePostfixOps p' (.callExpr base expr args)

    | .dot =>
      -- Member access - check for private identifier
      let p' ← p.advance
      let propToken := p'.peek
      match propToken.kind with
      | .privateIdentifier name =>
        -- Private member access: obj.#name
        let p'' ← p'.advance
        let propBase := makeBase propToken.pos propToken.endPos
        let privateName : PrivateName := { base := propBase, name }
        let base := makeBase (getExprStart expr) propToken.endPos
        parsePostfixOps p'' (.privateMemberExpr base expr privateName)
      | _ =>
        let p'' ← p'.advance
        let propBase := makeBase propToken.pos propToken.endPos
        -- Use resolved identifier name, not raw (which may contain unicode escapes)
        let propName := match propToken.kind with
          | .identifier name => name
          | _ => propToken.raw
        let prop := Expression.identifier propBase propName
        let base := makeBase (getExprStart expr) propToken.endPos
        parsePostfixOps p'' (.memberExpr base expr prop false)

    | .lbracket =>
      -- Computed member access
      let p' ← p.advance
      let (p'', prop) ← parseExpression p' 0
      let p''' ← p''.expect .rbracket "Expected ']'"
      let base := makeBase (getExprStart expr) p'''.peek.pos
      parsePostfixOps p''' (.memberExpr base expr prop true)

    | .plusplus =>
      -- Postfix ++
      let p' ← p.advance
      let base := makeBase (getExprStart expr) token.endPos
      parsePostfixOps p' (.updateExpr base .inc expr false)

    | .minusminus =>
      -- Postfix --
      let p' ← p.advance
      let base := makeBase (getExprStart expr) token.endPos
      parsePostfixOps p' (.updateExpr base .dec expr false)

    | .questiondot =>
      -- Optional chaining
      let p' ← p.advance
      if p'.check .lparen then
        -- Optional call
        let (p'', args) ← parseCallArguments p'
        let base := makeBase (getExprStart expr) p''.peek.pos
        let call := Expression.callExpr base expr args true
        parsePostfixOps p'' (.chainExpr base call)
      else if p'.check .lbracket then
        -- Optional computed member
        let p'' ← p'.advance
        let (p''', prop) ← parseExpression p'' 0
        let p'''' ← p'''.expect .rbracket "Expected ']'"
        let base := makeBase (getExprStart expr) p''''.peek.pos
        let member := Expression.memberExpr base expr prop true true
        parsePostfixOps p'''' (.chainExpr base member)
      else
        -- Optional member access
        let propToken := p'.peek
        let p'' ← p'.advance
        let propBase := makeBase propToken.pos propToken.endPos
        -- Use resolved identifier name, not raw (which may contain unicode escapes)
        let propName := match propToken.kind with
          | .identifier name => name
          | _ => propToken.raw
        let prop := Expression.identifier propBase propName
        let base := makeBase (getExprStart expr) propToken.endPos
        let member := Expression.memberExpr base expr prop false true
        parsePostfixOps p'' (.chainExpr base member)

    | .templateNoSub value raw =>
      -- Tagged template with no interpolations: tag`text`
      let p' ← p.advance
      let base := makeBase (getExprStart expr) token.endPos
      let element := TemplateElement.mk value raw true
      let quasi := Expression.templateLiteral base [element] []
      parsePostfixOps p' (.taggedTemplate base expr quasi)

    | .templateHead value raw =>
      -- Tagged template with interpolations: tag`text${expr}...`
      let (p', quasi) ← parseTemplateLiteral p (getExprStart expr) value raw
      let base := makeBase (getExprStart expr) p'.peek.pos
      parsePostfixOps p' (.taggedTemplate base expr quasi)

    -- TypeScript postfix operators: erase type and return expression unchanged
    | .as_ =>
      let p' ← p.advance
      let p'' ← skipTSTypeBalanced p'
      parsePostfixOps p'' expr

    | .satisfies =>
      let p' ← p.advance
      let p'' ← skipTSTypeBalanced p'
      parsePostfixOps p'' expr

    | .lt =>
      -- Generic call `f<T>(args)`, with backtracking when `<` is the comparison operator.
      match trySkipGenericArgs p with
      | some p' =>
        if p'.check .lparen then
          let (p'', callArgs) ← parseCallArguments p'
          let base := makeBase (getExprStart expr) p''.peek.pos
          parsePostfixOps p'' (.callExpr base expr callArgs)
        else
          return (p, expr)
      | none => return (p, expr)

    | _ => return (p, expr)

/-- Parse postfix expression (with call, member access, and postfix operators) -/
partial def parsePostfixExpr (p : ParserState) : ParseResult (ParserState × Expression) := do
  let (p', expr) ← parsePrimaryExpr p
  parsePostfixOps p' expr

/-- Parse call arguments -/
partial def parseCallArguments (p : ParserState) : ParseResult (ParserState × List Expression) := do
  let p' ← p.expect .lparen "Expected '('"
  let (p'', args) ← parseArgs p' []
  let p''' ← p''.expect .rparen "Expected ')'"
  return (p''', args)
where
  parseArgs (p : ParserState) (acc : List Expression) : ParseResult (ParserState × List Expression) := do
    if p.check .rparen then
      return (p, acc.reverse)
    else if p.check .ellipsis then
      -- Spread argument
      let startPos := p.peek.pos
      let p' ← p.advance
      let (p'', arg) ← parseAssignmentExpr p'
      let base := makeBase startPos p''.peek.pos
      let spread := Expression.spreadElement base arg
      if p''.check .comma then
        let p''' ← p''.advance
        parseArgs p''' (spread :: acc)
      else
        return (p'', (spread :: acc).reverse)
    else
      let (p', arg) ← parseAssignmentExpr p
      if p'.check .comma then
        let p'' ← p'.advance
        parseArgs p'' (arg :: acc)
      else
        return (p', (arg :: acc).reverse)

/-- Parse assignment expression -/
partial def parseAssignmentExpr (p : ParserState) : ParseResult (ParserState × Expression) := do
  parseExpression p 2  -- Assignment precedence level

/-- Parse assignment expression but exclude 'in' operator (for for-in/for-of LHS) -/
partial def parseAssignmentExprNoIn (p : ParserState) : ParseResult (ParserState × Expression) := do
  parseExpressionNoIn p 2

/-- Parse binary/ternary operators with Pratt precedence, excluding 'in' operator -/
partial def parseBinaryOpsNoIn (p : ParserState) (left : Expression) (minPrec : Nat) : ParseResult (ParserState × Expression) := do
  let token := p.peek
  -- Skip 'in' operator in this context
  if token.kind == .in then
    return (p, left)
  let prec := getOperatorPrecedence token.kind

  if prec == 0 || prec < minPrec then
    return (p, left)
  else
    -- Handle ternary operator specially
    if token.kind == .question then
      let p' ← p.advance
      let (p'', consequent) ← parseAssignmentExprNoIn p'
      let p''' ← p''.expect .colon "Expected ':' in ternary"
      let (p'''', alternate) ← parseAssignmentExprNoIn p'''
      let base := makeBase (getExprStart left) p''''.peek.pos
      let ternary := Expression.conditionalExpr base left consequent alternate
      parseBinaryOpsNoIn p'''' ternary minPrec
    else
      -- For right-associative operators, use same precedence; for left-associative, use prec+1
      let nextMinPrec := if isRightAssociative token.kind then prec else prec + 1
      let p' ← p.advance
      let (p'', right) ← parseExpressionNoIn p' nextMinPrec

      -- Create appropriate expression
      let base := makeBase (getExprStart left) p''.peek.pos
      let expr :=
        if token.kind == .comma then
          -- Comma operator: build a SequenceExpression, flattening nested sequences
          match left with
          | .sequenceExpr _ exprs => Expression.sequenceExpr base (exprs ++ [right])
          | _ => Expression.sequenceExpr base [left, right]
        else if let some op := tokenToLogicalOp token.kind then
          Expression.logicalExpr base op left right
        else if let some op := tokenToBinaryOp token.kind then
          Expression.binaryExpr base op left right
        else if let some op := tokenToAssignOp token.kind then
          Expression.assignmentExpr base op left right
        else
          left  -- Shouldn't happen

      parseBinaryOpsNoIn p'' expr minPrec

/-- Parse expression with Pratt parser, excluding 'in' operator -/
partial def parseExpressionNoIn (p : ParserState) (minPrec : Nat) : ParseResult (ParserState × Expression) := do
  -- Parse left side (unary/postfix expression)
  let (p', left) ← parseUnaryExpr p

  -- Parse binary/ternary operators (excluding 'in')
  parseBinaryOpsNoIn p' left minPrec

/-- Parse binary/ternary operators with Pratt precedence -/
partial def parseBinaryOps (p : ParserState) (left : Expression) (minPrec : Nat) : ParseResult (ParserState × Expression) := do
  let token := p.peek
  let prec := getOperatorPrecedence token.kind

  if prec == 0 || prec < minPrec then
    return (p, left)
  else
    -- Handle ternary operator specially
    if token.kind == .question then
      let p' ← p.advance
      let (p'', consequent) ← parseAssignmentExpr p'
      let p''' ← p''.expect .colon "Expected ':' in ternary"
      let (p'''', alternate) ← parseAssignmentExpr p'''
      let base := makeBase (getExprStart left) p''''.peek.pos
      let ternary := Expression.conditionalExpr base left consequent alternate
      parseBinaryOps p'''' ternary minPrec
    else
      -- For right-associative operators, use same precedence; for left-associative, use prec+1
      let nextMinPrec := if isRightAssociative token.kind then prec else prec + 1
      let p' ← p.advance
      let (p'', right) ← parseExpression p' nextMinPrec

      -- Create appropriate expression
      let base := makeBase (getExprStart left) p''.peek.pos
      let expr :=
        if token.kind == .comma then
          -- Comma operator: build a SequenceExpression, flattening nested sequences
          match left with
          | .sequenceExpr _ exprs => Expression.sequenceExpr base (exprs ++ [right])
          | _ => Expression.sequenceExpr base [left, right]
        else if let some op := tokenToLogicalOp token.kind then
          Expression.logicalExpr base op left right
        else if let some op := tokenToBinaryOp token.kind then
          Expression.binaryExpr base op left right
        else if let some op := tokenToAssignOp token.kind then
          Expression.assignmentExpr base op left right
        else
          left  -- Shouldn't happen

      parseBinaryOps p'' expr minPrec

/-- Parse expression with Pratt parser -/
partial def parseExpression (p : ParserState) (minPrec : Nat) : ParseResult (ParserState × Expression) := do
  -- Parse left side (unary/postfix expression)
  let (p', left) ← parseUnaryExpr p

  -- Parse binary/ternary operators
  parseBinaryOps p' left minPrec

/-- Parse a single statement -/
partial def parseStatement (p : ParserState) : ParseResult (ParserState × Statement) := do
  let token := p.peek
  let startPos := token.pos

  match token.kind with
  | .lbrace => parseBlockStmt p

  | .var | .let | .const => parseVariableDecl p

  | .if => parseIfStmt p

  | .while => parseWhileStmt p

  | .do => parseDoWhileStmt p

  | .for => parseForStmt p

  | .function => parseFunctionDecl p

  | .async =>
    -- Check if this is `async function` declaration by peeking at next token
    let isAsyncFunc : Bool := match nextToken p.lexer with
      | .ok (_, tok) => tok.kind == .function
      | .error _ => false
    if isAsyncFunc then
      parseAsyncFunctionDecl p
    else
      -- Fall through to expression statement (async arrow, etc.)
      let (p', expr) ← parseExpression p 0
      let base := makeBase startPos p'.peek.pos
      let p'' := if p'.check .semicolon then
        match p'.advance with | .ok pp => pp | .error _ => p'
      else p'
      return (p'', .exprStmt base expr)

  | .class => parseClassDecl p

  | .return =>
    let p' ← p.advance
    if p'.check .semicolon || p'.check .rbrace || p'.atEnd then
      let base := makeBase startPos p'.peek.pos
      let p'' := if p'.check .semicolon then
        match p'.advance with | .ok p => p | .error _ => p'
      else p'
      return (p'', .returnStmt base none)
    else
      let (p'', expr) ← parseExpression p' 0
      let base := makeBase startPos p''.peek.pos
      let p''' := if p''.check .semicolon then
        match p''.advance with | .ok p => p | .error _ => p''
      else p''
      return (p''', .returnStmt base (some expr))

  | .break =>
    let p' ← p.advance
    -- Check for label: break label;
    let (p'', labelOpt) := if let .identifier name := p'.peek.kind then
      let labelToken := p'.peek
      match p'.advance with
      | .ok p3 =>
        let id : Identifier := { base := makeBase labelToken.pos labelToken.endPos, name }
        (p3, some id)
      | .error _ => (p', none)
    else (p', none)
    let base := makeBase startPos p''.peek.pos
    let p''' := if p''.check .semicolon then
      match p''.advance with | .ok p => p | .error _ => p''
    else p''
    return (p''', .breakStmt base labelOpt)

  | .continue =>
    let p' ← p.advance
    -- Check for label: continue label;
    let (p'', labelOpt) := if let .identifier name := p'.peek.kind then
      let labelToken := p'.peek
      match p'.advance with
      | .ok p3 =>
        let id : Identifier := { base := makeBase labelToken.pos labelToken.endPos, name }
        (p3, some id)
      | .error _ => (p', none)
    else (p', none)
    let base := makeBase startPos p''.peek.pos
    let p''' := if p''.check .semicolon then
      match p''.advance with | .ok p => p | .error _ => p''
    else p''
    return (p''', .continueStmt base labelOpt)

  | .throw =>
    let p' ← p.advance
    let (p'', expr) ← parseExpression p' 0
    let base := makeBase startPos p''.peek.pos
    let p''' := if p''.check .semicolon then
      match p''.advance with | .ok p => p | .error _ => p''
    else p''
    return (p''', .throwStmt base expr)

  | .try => parseTryStmt p

  | .switch => parseSwitchStmt p

  | .semicolon =>
    let p' ← p.advance
    let base := makeBase startPos token.endPos
    return (p', .emptyStmt base)

  | .debugger =>
    let p' ← p.advance
    let base := makeBase startPos p'.peek.pos
    let p'' := if p'.check .semicolon then
      match p'.advance with | .ok p => p | .error _ => p'
    else p'
    return (p'', .debuggerStmt base)

  | .with =>
    let p' ← p.advance
    let p'' ← p'.expect .lparen "Expected '(' after 'with'"
    let (p''', object) ← parseExpression p'' 0
    let p'''' ← p'''.expect .rparen "Expected ')'"
    let (p5, body) ← parseStatement p''''
    let base := makeBase startPos p5.peek.pos
    return (p5, .withStmt base object body)

  | .identifier name =>
    -- Check if this is a labeled statement: identifier: statement
    -- We need to peek ahead to see if there's a colon
    let labelToken := token
    let p' ← p.advance
    if p'.check .colon then
      -- This is a labeled statement
      let p'' ← p'.advance
      let (p''', body) ← parseStatement p''
      let base := makeBase startPos p'''.peek.pos
      let label : Identifier := { base := makeBase labelToken.pos labelToken.endPos, name }
      return (p''', .labeledStmt base label body)
    else
      -- Regular expression statement starting with identifier
      -- We already consumed the identifier, so we need to continue parsing from there
      let idBase := makeBase labelToken.pos labelToken.endPos
      let idExpr := Expression.identifier idBase name
      -- Continue with postfix operations and binary operators
      let (p'', left) ← parsePostfixOps p' idExpr
      let (p''', expr) ← parseBinaryOps p'' left 0
      let base := makeBase startPos p'''.peek.pos
      let p'''' := if p'''.check .semicolon then
        match p'''.advance with | .ok pp => pp | .error _ => p'''
      else p'''
      return (p'''', .exprStmt base expr)

  -- In non-strict mode, 'yield' and 'await' can be used as labels
  -- Check for labeled statement: yield: statement or await: statement
  | .yield | .await =>
    -- Peek ahead to check for colon (label syntax)
    let labelToken := token
    let labelName := if token.kind == .yield then "yield" else "await"
    let p' ← p.advance
    if p'.check .colon then
      -- This is a labeled statement
      let p'' ← p'.advance
      let (p''', body) ← parseStatement p''
      let base := makeBase startPos p'''.peek.pos
      let label : Identifier := { base := makeBase labelToken.pos labelToken.endPos, name := labelName }
      return (p''', .labeledStmt base label body)
    else
      -- Not a label - fall through to expression statement parsing
      -- parseExpression handles yield/await properly (as yield/await expressions)
      let (p'', expr) ← parseExpression p 0
      let base := makeBase startPos p''.peek.pos
      let p''' := if p''.check .semicolon then
        match p''.advance with | .ok pp => pp | .error _ => p''
      else p''
      return (p''', .exprStmt base expr)

  | .interface =>
    -- Parse interface declaration inline (skip it, emit empty statement).
    let mut ps ← p.advance  -- skip 'interface'
    ps ← ps.advance         -- skip name
    if ps.check .lt then
      ps ← ps.advance
      let mut depth : Nat := 1
      while depth > 0 do
        if ps.check .lt then depth := depth + 1
        else if ps.check .gt then depth := depth - 1
        ps ← ps.advance
    if ps.check .extends then
      ps ← ps.advance
      while !ps.check .lbrace && !ps.atEnd do
        ps ← ps.advance
    ps ← ps.expect .lbrace "Expected '{' in interface declaration"
    let mut braceDepth : Nat := 1
    while braceDepth > 0 do
      if ps.check .lbrace then braceDepth := braceDepth + 1
      else if ps.check .rbrace then braceDepth := braceDepth - 1
      if braceDepth > 0 then
        ps ← ps.advance
    ps ← ps.advance  -- skip final '}'
    let base := makeBase startPos ps.peek.pos
    return (ps, .emptyStmt base)

  | _ =>
    -- Expression statement
    let (p', expr) ← parseExpression p 0
    let base := makeBase startPos p'.peek.pos
    let p'' := if p'.check .semicolon then
      match p'.advance with | .ok pp => pp | .error _ => p'
    else p'
    return (p'', .exprStmt base expr)

/-- Parse variable declaration -/
partial def parseVariableDecl (p : ParserState) : ParseResult (ParserState × Statement) := do
  let startPos := p.peek.pos
  let kind := match p.peek.kind with
    | .var => VariableKind.var
    | .let => VariableKind.let_
    | .const => VariableKind.const
    | _ => VariableKind.var

  let p' ← p.advance
  let (p'', declarators) ← parseDeclarators p' []
  let base := makeBase startPos p''.peek.pos

  let p''' := if p''.check .semicolon then
    match p''.advance with | .ok pp => pp | .error _ => p''
  else p''

  let decl := VariableDeclaration.mk base declarators kind
  return (p''', .variableDecl decl)
where
  -- Check if a token can be used as an identifier (including contextual keywords)
  isIdentifierLike (kind : TokenKind) : Bool :=
    match kind with
    | .identifier _ => true
    -- Contextual keywords that can be identifiers in non-strict mode
    | .await | .yield | .static | .get | .set | .async | .of => true
    | _ => false

  getIdentifierName (kind : TokenKind) (raw : String) : String :=
    match kind with
    | .identifier name => name
    | _ => raw  -- For keywords, use the raw token value

  parseDeclarators (p : ParserState) (acc : List VariableDeclarator) : ParseResult (ParserState × List VariableDeclarator) := do
    let token := p.peek
    let startPos := token.pos
    if isIdentifierLike token.kind then
      let name := getIdentifierName token.kind token.raw
      let p' ← p.advance
      let id : Identifier := { base := makeBase token.pos token.endPos, name }
      let pattern := Pattern.identifier id
      -- Parse optional `?` and type annotation: name?: Type or name: Type
      let pa := if p'.check .question then
        match p'.advance with | .ok pp => pp | .error _ => p'
      else p'
      let (p'pre, typeAnn) ← if pa.check .colon then do
        let pb ← pa.advance
        let (pc, ty) ← parseTypeExpression pb
        pure (pc, some ty)
      else
        pure (pa, none)
      -- Parse initializer (TS `as T`/`satisfies T` postfix handled in parsePostfixOps)
      let (p'', init) ← if p'pre.check .assign then do
        let p2 ← p'pre.advance
        let (p3, expr) ← parseAssignmentExpr p2
        pure (p3, some expr)
      else
        pure (p'pre, none)
      let base := makeBase startPos p''.peek.pos
      let decl := VariableDeclarator.mk base pattern init typeAnn
      if p''.check .comma then
        match p''.advance with
        | .ok p3 => parseDeclarators p3 (decl :: acc)
        | .error _ => return (p'', (decl :: acc).reverse)
      else
        return (p'', (decl :: acc).reverse)
    else if token.kind == .lbracket then
      -- Array destructuring: const [a, b] = arr
      let (p', arrExpr) ← parseArrayLiteral p
      let pattern ← exprToPattern arrExpr
      -- Skip optional type annotation: [x]: Type = ...
      let p' ← if p'.check .colon then do
        let mut ps ← p'.advance
        let mut depth : Nat := 0
        while !(ps.check .assign && depth == 0) && !ps.atEnd do
          if ps.check .lbrace || ps.check .lbracket || ps.check .lparen || ps.check .lt then
            depth := depth + 1
          else if ps.check .rbrace || ps.check .rbracket || ps.check .rparen || ps.check .gt then
            if depth > 0 then depth := depth - 1
          ps ← ps.advance
        pure ps
      else
        pure p'
      let p'' ← p'.expect .assign "Expected '=' in destructuring declaration"
      let (p''', init) ← parseAssignmentExpr p''
      let base := makeBase startPos p'''.peek.pos
      let decl := VariableDeclarator.mk base pattern (some init)
      if p'''.check .comma then
        match p'''.advance with
        | .ok p4 => parseDeclarators p4 (decl :: acc)
        | .error _ => return (p''', (decl :: acc).reverse)
      else
        return (p''', (decl :: acc).reverse)
    else if token.kind == .lbrace then
      -- Object destructuring: const { a, b } = obj
      let (p', objExpr) ← parseObjectLiteral p
      let pattern ← exprToPattern objExpr
      -- Skip optional type annotation: { x }: Type = ...
      let p' ← if p'.check .colon then do
        let mut ps ← p'.advance
        let mut depth : Nat := 0
        while !(ps.check .assign && depth == 0) && !ps.atEnd do
          if ps.check .lbrace || ps.check .lbracket || ps.check .lparen || ps.check .lt then
            depth := depth + 1
          else if ps.check .rbrace || ps.check .rbracket || ps.check .rparen || ps.check .gt then
            if depth > 0 then depth := depth - 1
          ps ← ps.advance
        pure ps
      else
        pure p'
      let p'' ← p'.expect .assign "Expected '=' in destructuring declaration"
      let (p''', init) ← parseAssignmentExpr p''
      let base := makeBase startPos p'''.peek.pos
      let decl := VariableDeclarator.mk base pattern (some init)
      if p'''.check .comma then
        match p'''.advance with
        | .ok p4 => parseDeclarators p4 (decl :: acc)
        | .error _ => return (p''', (decl :: acc).reverse)
      else
        return (p''', (decl :: acc).reverse)
    else
      throw s!"Expected identifier or pattern in variable declaration, got {repr token.kind}"

/-- Parse if statement -/
partial def parseIfStmt (p : ParserState) : ParseResult (ParserState × Statement) := do
  let startPos := p.peek.pos
  let p' ← p.expect .if "Expected 'if'"
  let p'' ← p'.expect .lparen "Expected '('"
  let (p''', test) ← parseExpression p'' 0
  let p'''' ← p'''.expect .rparen "Expected ')'"
  let (p5, consequent) ← parseStatement p''''

  let (p6, alternate) := if p5.check .else then
    match p5.advance with
    | .ok p' =>
      match parseStatement p' with
      | .ok (p'', stmt) => (p'', some stmt)
      | .error _ => (p5, none)
    | .error _ => (p5, none)
  else (p5, none)

  let base := makeBase startPos p6.peek.pos
  return (p6, .ifStmt base test consequent alternate)

/-- Parse while statement -/
partial def parseWhileStmt (p : ParserState) : ParseResult (ParserState × Statement) := do
  let startPos := p.peek.pos
  let p' ← p.expect .while "Expected 'while'"
  let p'' ← p'.expect .lparen "Expected '('"
  let (p''', test) ← parseExpression p'' 0
  let p'''' ← p'''.expect .rparen "Expected ')'"
  let (p5, body) ← parseStatement p''''

  let base := makeBase startPos p5.peek.pos
  return (p5, .whileStmt base test body)

/-- Parse do-while statement -/
partial def parseDoWhileStmt (p : ParserState) : ParseResult (ParserState × Statement) := do
  let startPos := p.peek.pos
  let p' ← p.expect .do "Expected 'do'"
  let (p'', body) ← parseStatement p'
  let p''' ← p''.expect .while "Expected 'while'"
  let p'''' ← p'''.expect .lparen "Expected '('"
  let (p5, test) ← parseExpression p'''' 0
  let p6 ← p5.expect .rparen "Expected ')'"
  let p7 := if p6.check .semicolon then
    match p6.advance with | .ok pp => pp | .error _ => p6
  else p6

  let base := makeBase startPos p7.peek.pos
  return (p7, .doWhileStmt base body test)

/-- Parse for statement -/
partial def parseForStmt (p : ParserState) : ParseResult (ParserState × Statement) := do
  let startPos := p.peek.pos
  let p' ← p.expect .for "Expected 'for'"

  -- Check for `for await`
  let (p'', isForAwait) := if p'.check .await then
    match p'.advance with
    | .ok p3 => (p3, true)
    | .error _ => (p', false)
  else (p', false)

  let p''' ← p''.expect .lparen "Expected '('"

  -- Try to parse for-in/for-of first, or fall back to standard for loop
  if p'''.check .semicolon then
    -- Empty init: for (;;) or for(; test; update)
    if isForAwait then
      throw "for await requires for-of syntax"
    let p4 ← p'''.advance
    parseStandardFor p4 startPos none
  -- Special case: `for (let in obj)` - 'let' is an identifier, not a keyword
  -- 'let' is only a keyword here when followed by an identifier, [, or {
  else if p'''.check .let then
    -- Peek ahead to check what follows 'let'
    -- If followed directly by 'in' or 'of', treat 'let' as an identifier
    let isLetAsIdentifier :=
      let p4Test := match p'''.advance with
        | .ok p4 => p4
        | .error _ => p'''
      p4Test.check .in || p4Test.check .of
    if isLetAsIdentifier then
      -- Treat 'let' as an identifier
      let letToken := p'''.peek
      let p4 ← p'''.advance
      let idBase := makeBase letToken.pos letToken.endPos
      let letExpr := Expression.identifier idBase "let"
      -- Now check for 'in' or 'of'
      if p4.check .in then
        if isForAwait then
          throw "for await requires for-of syntax, not for-in"
        let p5 ← p4.advance
        let (p6, right) ← parseExpression p5 0
        let p7 ← p6.expect .rparen "Expected ')'"
        let (p8, body) ← parseStatement p7
        let base := makeBase startPos p8.peek.pos
        return (p8, .forInStmt base (.inl letExpr) right body)
      else if p4.check .of then
        let p5 ← p4.advance
        let (p6, right) ← parseAssignmentExpr p5
        let p7 ← p6.expect .rparen "Expected ')'"
        let (p8, body) ← parseStatement p7
        let base := makeBase startPos p8.peek.pos
        return (p8, .forOfStmt base (.inl letExpr) right body isForAwait)
      else
        throw "Expected 'in' or 'of' after 'let' in for loop"
    else
      -- 'let' is a keyword - parse as variable declaration
      let kind := VariableKind.let_
      let p4 ← p'''.advance
      let (p5, declarators) ← parseVarDeclList p4 []
      -- Check for for-in or for-of
      if p5.check .in then
        if isForAwait then
          throw "for await requires for-of syntax, not for-in"
        let p6 ← p5.advance
        let (p7, right) ← parseExpression p6 0
        let p8 ← p7.expect .rparen "Expected ')'"
        let (p9, body) ← parseStatement p8
        let base := makeBase startPos p9.peek.pos
        let decl := VariableDeclaration.mk {} declarators kind
        return (p9, .forInStmt base (.inr decl) right body)
      else if p5.check .of then
        let p6 ← p5.advance
        let (p7, right) ← parseAssignmentExpr p6
        let p8 ← p7.expect .rparen "Expected ')'"
        let (p9, body) ← parseStatement p8
        let base := makeBase startPos p9.peek.pos
        let decl := VariableDeclaration.mk {} declarators kind
        return (p9, .forOfStmt base (.inr decl) right body isForAwait)
      else
        if isForAwait then
          throw "for await requires for-of syntax"
        let p6 ← p5.expect .semicolon "Expected ';'"
        let decl := VariableDeclaration.mk {} declarators kind
        parseStandardFor p6 startPos (some (.inr decl))
  else if p'''.check .var || p'''.check .const then
    let kind := match p'''.peek.kind with
      | .var => VariableKind.var
      | _ => VariableKind.const
    let p4 ← p'''.advance
    let (p5, declarators) ← parseVarDeclList p4 []
    -- Check for for-in or for-of
    if p5.check .in then
      if isForAwait then
        throw "for await requires for-of syntax, not for-in"
      let p6 ← p5.advance
      let (p7, right) ← parseExpression p6 0
      let p8 ← p7.expect .rparen "Expected ')'"
      let (p9, body) ← parseStatement p8
      let base := makeBase startPos p9.peek.pos
      let decl := VariableDeclaration.mk {} declarators kind
      return (p9, .forInStmt base (.inr decl) right body)
    else if p5.check .of then
      let p6 ← p5.advance
      let (p7, right) ← parseAssignmentExpr p6
      let p8 ← p7.expect .rparen "Expected ')'"
      let (p9, body) ← parseStatement p8
      let base := makeBase startPos p9.peek.pos
      let decl := VariableDeclaration.mk {} declarators kind
      return (p9, .forOfStmt base (.inr decl) right body isForAwait)
    else
      if isForAwait then
        throw "for await requires for-of syntax"
      let p6 ← p5.expect .semicolon "Expected ';'"
      let decl := VariableDeclaration.mk {} declarators kind
      parseStandardFor p6 startPos (some (.inr decl))
  else
    -- Use NoIn parser to prevent 'in' being consumed as binary operator
    let (p4, expr) ← parseExpressionNoIn p''' 0
    -- Check for for-in or for-of
    if p4.check .in then
      if isForAwait then
        throw "for await requires for-of syntax, not for-in"
      let p5 ← p4.advance
      let (p6, right) ← parseExpression p5 0
      let p7 ← p6.expect .rparen "Expected ')'"
      let (p8, body) ← parseStatement p7
      let base := makeBase startPos p8.peek.pos
      -- Convert array/object expressions to destructuring patterns
      let leftExpr ← match expr with
        | .arrayExpr b _ | .objectExpr b _ =>
          let pat ← exprToPattern expr
          pure (.patternExpr b pat)
        | _ => pure expr
      return (p8, .forInStmt base (.inl leftExpr) right body)
    else if p4.check .of then
      let p5 ← p4.advance
      let (p6, right) ← parseAssignmentExpr p5
      let p7 ← p6.expect .rparen "Expected ')'"
      let (p8, body) ← parseStatement p7
      let base := makeBase startPos p8.peek.pos
      -- Convert array/object expressions to destructuring patterns
      let leftExpr ← match expr with
        | .arrayExpr b _ | .objectExpr b _ =>
          let pat ← exprToPattern expr
          pure (.patternExpr b pat)
        | _ => pure expr
      return (p8, .forOfStmt base (.inl leftExpr) right body isForAwait)
    else
      if isForAwait then
        throw "for await requires for-of syntax"
      let p5 ← p4.expect .semicolon "Expected ';'"
      parseStandardFor p5 startPos (some (.inl expr))
where
  parseStandardFor (p : ParserState) (startPos : Position)
      (init : Option (Expression ⊕ VariableDeclaration)) : ParseResult (ParserState × Statement) := do
    -- Parse test
    let (p', test) := if p.check .semicolon then (p, none)
      else match parseExpression p 0 with
        | .ok (ps, expr) => (ps, some expr)
        | .error _ => (p, none)
    let p'' ← p'.expect .semicolon "Expected ';'"

    -- Parse update
    let (p''', update) := if p''.check .rparen then (p'', none)
      else match parseExpression p'' 0 with
        | .ok (ps, expr) => (ps, some expr)
        | .error _ => (p'', none)
    let p'''' ← p'''.expect .rparen "Expected ')'"

    let (p5, body) ← parseStatement p''''
    let base := makeBase startPos p5.peek.pos
    return (p5, .forStmt base init test update body)

  parseVarDeclList (p : ParserState) (acc : List VariableDeclarator) : ParseResult (ParserState × List VariableDeclarator) := do
    let token := p.peek
    let startPos := token.pos
    match token.kind with
    | .identifier name =>
      let p' ← p.advance
      let id : Identifier := { base := makeBase token.pos token.endPos, name }
      let pattern := Pattern.identifier id
      -- Use NoIn parser to avoid consuming 'in' as binary operator in initializer
      let (p'', init) := if p'.check .assign then
        match p'.advance with
        | .ok p2 =>
          match parseAssignmentExprNoIn p2 with
          | .ok (p3, expr) => (p3, some expr)
          | .error _ => (p', none)
        | .error _ => (p', none)
      else (p', none)
      let base := makeBase startPos p''.peek.pos
      let decl := VariableDeclarator.mk base pattern init
      if p''.check .comma then
        match p''.advance with
        | .ok p3 => parseVarDeclList p3 (decl :: acc)
        | .error _ => return (p'', (decl :: acc).reverse)
      else
        return (p'', (decl :: acc).reverse)
    | .lbracket =>
      -- Array destructuring in for loop: for (const [a, b] of arr)
      let (p', arrExpr) ← parseArrayLiteral p
      let pattern ← exprToPattern arrExpr
      -- In for-of/for-in, the init is optional (just the pattern, no = ...)
      -- Use NoIn parser to avoid consuming 'in' as binary operator
      let (p'', init) := if p'.check .assign then
        match p'.advance with
        | .ok p2 =>
          match parseAssignmentExprNoIn p2 with
          | .ok (p3, expr) => (p3, some expr)
          | .error _ => (p', none)
        | .error _ => (p', none)
      else (p', none)
      let base := makeBase startPos p''.peek.pos
      let decl := VariableDeclarator.mk base pattern init
      if p''.check .comma then
        match p''.advance with
        | .ok p3 => parseVarDeclList p3 (decl :: acc)
        | .error _ => return (p'', (decl :: acc).reverse)
      else
        return (p'', (decl :: acc).reverse)
    | .lbrace =>
      -- Object destructuring in for loop: for (const { a, b } of arr)
      let (p', objExpr) ← parseObjectLiteral p
      let pattern ← exprToPattern objExpr
      -- Use NoIn parser to avoid consuming 'in' as binary operator
      let (p'', init) := if p'.check .assign then
        match p'.advance with
        | .ok p2 =>
          match parseAssignmentExprNoIn p2 with
          | .ok (p3, expr) => (p3, some expr)
          | .error _ => (p', none)
        | .error _ => (p', none)
      else (p', none)
      let base := makeBase startPos p''.peek.pos
      let decl := VariableDeclarator.mk base pattern init
      if p''.check .comma then
        match p''.advance with
        | .ok p3 => parseVarDeclList p3 (decl :: acc)
        | .error _ => return (p'', (decl :: acc).reverse)
      else
        return (p'', (decl :: acc).reverse)
    | _ => throw s!"Expected identifier or pattern in variable declaration"

/-- Parse function declaration -/
partial def parseFunctionDecl (p : ParserState) : ParseResult (ParserState × Statement) := do
  let startPos := p.peek.pos
  let p' ← p.expect .function "Expected 'function'"

  -- Check for generator: function*
  let (p'', isGenerator) := if p'.check .star then
    match p'.advance with
    | .ok p3 => (p3, true)
    | .error _ => (p', false)
  else (p', false)

  -- Parse name (required for declarations)
  let token := p''.peek
  match token.kind with
  | .identifier name =>
    let p''' ← p''.advance
    let id : Identifier := { base := makeBase token.pos token.endPos, name }
    -- Skip optional generic type parameters <T, U extends ...>
    let p''' :=
      match trySkipGenericArgs p''' with
      | some p4 => p4
      | none => p'''
    let (p'''', func) ← parseFunctionBody p''' (some id) isGenerator false
    let base := makeBase startPos p''''.peek.pos
    match func with
    | .functionExpr _ _ params body gen async =>
      return (p'''', .functionDecl base id params body gen async)
    | _ => throw "Internal error"
  | _ => throw "Expected function name"

/-- Parse async function declaration: async function name(...) { ... } -/
partial def parseAsyncFunctionDecl (p : ParserState) : ParseResult (ParserState × Statement) := do
  let startPos := p.peek.pos
  let p' ← p.expect .async "Expected 'async'"
  let p'' ← p'.expect .function "Expected 'function'"

  -- Check for generator: async function*
  let (p''', isGenerator) := if p''.check .star then
    match p''.advance with
    | .ok p3 => (p3, true)
    | .error _ => (p'', false)
  else (p'', false)

  -- Parse name (required for declarations)
  let token := p'''.peek
  match token.kind with
  | .identifier name =>
    let p4 ← p'''.advance
    let id : Identifier := { base := makeBase token.pos token.endPos, name }
    -- Skip optional generic type parameters <T, U extends ...>
    let p4 :=
      match trySkipGenericArgs p4 with
      | some p4' => p4'
      | none => p4
    let (p5, func) ← parseFunctionBody p4 (some id) isGenerator true
    let base := makeBase startPos p5.peek.pos
    match func with
    | .functionExpr _ _ params body gen _ =>
      return (p5, .functionDecl base id params body gen true)
    | _ => throw "Internal error: expected function expression from parseFunctionBody"
  | _ => throw "Expected function name after 'async function'"

/-- Parse class declaration -/
partial def parseClassDecl (p : ParserState) (isAbstract : Bool := false) : ParseResult (ParserState × Statement) := do
  let startPos := p.peek.pos
  let p' ← p.expect .class "Expected 'class'"

  -- Parse name (required for declarations)
  let token := p'.peek
  match token.kind with
  | .identifier name =>
    let p'' ← p'.advance
    let id : Identifier := { base := makeBase token.pos token.endPos, name }

    -- Skip optional generic type parameters: class Foo<T, U> { ... }
    let (p'', hasTypeParams) :=
      match trySkipGenericArgs p'' with
      | some p3 => (p3, true)
      | none => (p'', false)

    -- Optional extends clause
    let (p''', superClass) := if p''.check .extends then
      match p''.advance with
      | .ok p3 =>
        match parseUnaryExpr p3 with
        | .ok (p4, expr) => (p4, some expr)
        | .error _ => (p'', none)
      | .error _ => (p'', none)
    else (p'', none)

    -- Optional implements clause: implements I, J
    let (p3i, hasImplements) ← skipImplementsClause p'''

    -- Parse class body
    let (p'''', methods) ← parseClassBody p3i

    let base := makeBase startPos p''''.peek.pos
    return (p'''', .classDecl base id superClass methods isAbstract hasTypeParams hasImplements)
  | _ => throw "Expected class name"

/-- Parse catch clause parameter (identifier or destructuring pattern). Returns
    the optional type annotation name when the parameter is a simple `e: E`. -/
partial def parseCatchParam (p : ParserState) : ParseResult (ParserState × Option Pattern × Option String) := do
  let token := p.peek
  match token.kind with
  | .identifier name =>
    let p' ← p.advance
    let id : Identifier := { base := makeBase token.pos token.endPos, name }
    let (p', catchTypeName) ← if p'.check .colon then do
      let pa ← p'.advance
      let (pb, ty) ← parseTypeExpression pa
      let typeName : Option String := match ty with
        | .ref n _ => some n
        | _ => none
      pure (pb, typeName)
    else pure (p', none)
    return (p', some (Pattern.identifier id), catchTypeName)
  | .lbracket =>
    -- Array destructuring: catch ([a, b]) {}
    let (p', arrExpr) ← parseArrayLiteral p
    let pattern ← exprToPattern arrExpr
    return (p', some pattern, none)
  | .lbrace =>
    -- Object destructuring: catch ({ message }) {}
    let (p', objExpr) ← parseObjectLiteral p
    let pattern ← exprToPattern objExpr
    return (p', some pattern, none)
  | _ =>
    throw s!"Expected catch parameter (identifier or pattern), got {repr token.kind}"

/-- Parse try statement -/
partial def parseTryStmt (p : ParserState) : ParseResult (ParserState × Statement) := do
  let startPos := p.peek.pos
  let p' ← p.expect .try "Expected 'try'"
  let (p'', block) ← parseBlockStmt p'

  let (p''', handler) := if p''.check .catch then
    match p''.advance with
    | .ok p3 =>
      -- Check for optional catch binding (catch without parameter)
      let (p4, param, catchType) := if p3.check .lparen then
        match p3.advance with
        | .ok p4' =>
          -- Check for empty parens: catch () {} - not valid JS but handle gracefully
          if p4'.check .rparen then
            match p4'.advance with
            | .ok p5 => (p5, none, none)
            | .error _ => (p3, none, none)
          else
            -- Parse catch parameter (with optional TS type annotation)
            match parseCatchParam p4' with
            | .ok (p5, paramOpt, catchTypeName) =>
              match p5.expect .rparen "Expected ')'" with
              | .ok p6 => (p6, paramOpt, catchTypeName)
              | .error _ => (p3, none, none)
            | .error _ => (p3, none, none)
        | .error _ => (p3, none, none)
      else (p3, none, none)  -- Optional catch binding: catch { }
      match parseBlockStmt p4 with
      | .ok (p5, body) =>
        let clause := CatchClause.mk {} param body catchType
        (p5, some clause)
      | .error _ => (p'', none)
    | .error _ => (p'', none)
  else (p'', none)

  let (p'''', finalizer) := if p'''.check .finally then
    match p'''.advance with
    | .ok p4 =>
      match parseBlockStmt p4 with
      | .ok (p5, stmt) => (p5, some stmt)
      | .error _ => (p''', none)
    | .error _ => (p''', none)
  else (p''', none)

  let base := makeBase startPos p''''.peek.pos
  return (p'''', .tryStmt base block handler finalizer)

/-- Parse switch statement -/
partial def parseSwitchStmt (p : ParserState) : ParseResult (ParserState × Statement) := do
  let startPos := p.peek.pos
  let p' ← p.expect .switch "Expected 'switch'"
  let p'' ← p'.expect .lparen "Expected '('"
  let (p''', discriminant) ← parseExpression p'' 0
  let p'''' ← p'''.expect .rparen "Expected ')'"
  let p5 ← p''''.expect .lbrace "Expected '{'"

  let (p6, cases) ← parseCases p5 []

  let p7 ← p6.expect .rbrace "Expected '}'"
  let base := makeBase startPos p7.peek.pos
  return (p7, .switchStmt base discriminant cases)
where
  parseCases (p : ParserState) (acc : List SwitchCase) : ParseResult (ParserState × List SwitchCase) := do
    if p.check .rbrace then
      return (p, acc.reverse)
    else if p.check .case then
      let p' ← p.advance
      let (p'', test) ← parseExpression p' 0
      let p''' ← p''.expect .colon "Expected ':'"
      let (p'''', stmts) ← parseCaseBody p''' []
      let case := SwitchCase.mk {} (some test) stmts
      parseCases p'''' (case :: acc)
    else if p.check .default then
      let p' ← p.advance
      let p'' ← p'.expect .colon "Expected ':'"
      let (p''', stmts) ← parseCaseBody p'' []
      let case := SwitchCase.mk {} none stmts
      parseCases p''' (case :: acc)
    else
      throw "Expected 'case' or 'default'"

  parseCaseBody (p : ParserState) (acc : List Statement) : ParseResult (ParserState × List Statement) := do
    if p.check .rbrace || p.check .case || p.check .default then
      return (p, acc.reverse)
    else
      let (p', stmt) ← parseStatement p
      parseCaseBody p' (stmt :: acc)

end

/-- Parse program (list of statements) -/
partial def parseProgram (p : ParserState) : ParseResult (ParserState × Program) := do
  let (p', stmts) ← parseStatements p []
  return (p', { body := stmts, sourceType := "script" })
where
  parseStatements (p : ParserState) (acc : List Statement) : ParseResult (ParserState × List Statement) := do
    if p.atEnd then
      return (p, acc.reverse)
    else
      let (p', stmt) ← parseStatement p
      parseStatements p' (stmt :: acc)


/-- Parse generic type parameter list: <T, U extends Foo, V = Bar> -/
partial def parseTypeParams (p : ParserState) :
    ParseResult (ParserState × List TSTypeParam) := do
  if !p.check .lt then
    return (p, [])
  let p1 ← p.advance  -- skip <
  let mut ps := p1
  let mut params : List TSTypeParam := []
  while !ps.check .gt do
    if !params.isEmpty then
      ps ← ps.expect .comma "Expected ',' between type parameters"
    let name ← match ps.current.kind with
      | .identifier n => pure n
      | _ => throw s!"Expected type parameter name at line {ps.current.pos.line}"
    ps ← ps.advance
    -- Check for constraint: extends Type
    let (ps', constraint) ← if ps.check .extends then
      let pa ← ps.advance
      let (pb, ty) ← parseTypeExpression pa
      pure (pb, some ty)
    else
      pure (ps, none)
    -- Check for default: = Type
    let (ps'', default_) ← if ps'.check .assign then
      let pa ← ps'.advance
      let (pb, ty) ← parseTypeExpression pa
      pure (pb, some ty)
    else
      pure (ps', none)
    ps := ps''
    params := params ++ [{ name, constraint, default_ }]
  ps ← ps.expect .gt "Expected '>' to close type parameter list"
  return (ps, params)

/-- Strip TS expression wrappers, returning the underlying JS expression -/
partial def stripTSExpr : TSExpression → Expression
  | .js e => e
  | .asExpr inner _ => stripTSExpr inner
  | .satisfiesExpr inner _ => stripTSExpr inner
  | .nonNullAssert inner => stripTSExpr inner

/-- Wrap a JS expression with TS postfix operators: as T, satisfies T, ! -/
partial def parseTSExpressionWrap (p : ParserState) (minPrec : Nat := 0) :
    ParseResult (ParserState × TSExpression) := do
  let (p1, jsExpr) ← parseExpression p minPrec
  parseTSPostfixOps p1 (.js jsExpr)
where
  parseTSPostfixOps (p : ParserState) (expr : TSExpression) :
      ParseResult (ParserState × TSExpression) := do
    match p.current.kind with
    | .as_ =>
      let p1 ← p.advance
      let (p2, ty) ← parseTypeExpression p1
      parseTSPostfixOps p2 (.asExpr expr ty)
    | .satisfies =>
      let p1 ← p.advance
      let (p2, ty) ← parseTypeExpression p1
      parseTSPostfixOps p2 (.satisfiesExpr expr ty)
    | .bang =>
      let p1 ← p.advance
      parseTSPostfixOps p1 (.nonNullAssert expr)
    | _ => return (p, expr)

/-- Parse a TS variable declaration: let x: T = expr; -/
partial def parseTSVariableDecl (p : ParserState) (kind : VariableKind) :
    ParseResult (ParserState × TSStatement) := do
  let startPos := p.current.pos
  let p1 ← p.advance  -- skip let/const/var
  -- Check for destructuring pattern — delegate to JS parser
  if p1.check .lbracket || p1.check .lbrace then
    let (p2, stmt) ← parseVariableDecl p  -- start from 'p' (before let/const/var)
    return (p2, .js stmt)
  let name ← match p1.current.kind with
    | .identifier n => pure n
    | _ => throw s!"Expected identifier in variable declaration at line {p1.current.pos.line}"
  let p2 ← p1.advance
  -- Check for type annotation
  let (p3, typeAnn) ← if p2.check .colon then
    let pa ← p2.advance
    let (pb, ty) ← parseTypeExpression pa
    pure (pb, some (TypeAnnotation.mk ty))
  else
    pure (p2, none)
  -- Check for initializer
  let (p4, init) ← if p3.check .assign then
    let pa ← p3.advance
    let (pb, tsExpr) ← parseTSExpressionWrap pa
    pure (pb, some (stripTSExpr tsExpr))
  else
    pure (p3, none)
  -- Consume optional semicolon
  let p5 := if p4.check .semicolon then
    match p4.advance with | .ok pp => pp | .error _ => p4
  else p4
  return (p5, .annotatedVarDecl (makeBase startPos startPos) kind name typeAnn init)


/-- Parse a TS function declaration -/
partial def parseTSFunctionDecl (p : ParserState) :
    ParseResult (ParserState × TSStatement) := do
  let startPos := p.current.pos
  -- Capture any JSDoc directives that preceded this `function` keyword.
  -- `skipWhitespaceAndComments` stores the most recently scanned `/** */`
  -- block in `p.lexer.lastJSDoc`; read it here before advancing.
  -- Clear the field after capture so the next function doesn't inherit
  -- the previous function's directives.
  let jsDoc := p.lexer.lastJSDoc
  let p := { p with lexer := { p.lexer with lastJSDoc := {} } }
  let p1 ← p.advance  -- skip 'function'
  let name ← match p1.current.kind with
    | .identifier n => pure n
    | _ => throw s!"Expected function name at line {p1.current.pos.line}"
  let p2 ← p1.advance
  let (p3, typeParams) ← parseTypeParams p2
  let (p4, params) ← parseTSFunctionParams p3
  let (p5, returnType) ← if p4.check .colon then
    let pa ← p4.advance
    let (pb, ty) ← parseTypeExpression pa
    pure (pb, some (TypeAnnotation.mk ty))
  else
    pure (p4, none)
  -- Ambient function declarations (declare function f(): void;) have no body
  if p5.check .semicolon then
    let p6 ← p5.advance
    return (p6, .annotatedFuncDecl (makeBase startPos startPos) name typeParams params returnType (.blockStmt {} [])
      (throwsAnn := jsDoc.throwsAnn) (total := jsDoc.total))
  let (p6, body) ← parseBlockStmt p5
  return (p6, .annotatedFuncDecl (makeBase startPos startPos) name typeParams params returnType body
    (throwsAnn := jsDoc.throwsAnn) (total := jsDoc.total))

/-- Parse interface members: { name: Type; name: Type; } -/
partial def parseInterfaceMembers (p : ParserState) :
    ParseResult (ParserState × List TSInterfaceMember) := do
  let p1 ← p.expect .lbrace "Expected '{' after interface name"
  let mut ps := p1
  let mut members : List TSInterfaceMember := []
  while !ps.check .rbrace do
    let isReadonly := ps.check .readonly
    if isReadonly then
      ps := match ps.advance with | .ok pp => pp | .error _ => ps
    if ps.check .lbracket then
      -- Could be index signature [key: Type]: ValueType or computed property [expr]: Type
      -- Disambiguate: peek after identifier — if next is ':', it's an index signature
      let isIndexSig := match ps.advance with
        | .ok p2 =>
          match p2.current.kind with
          | .identifier _ =>
            match p2.advance with
            | .ok p3 => p3.check .colon
            | .error _ => false
          | _ => false
        | .error _ => false
      if isIndexSig then
        -- Index signature: [key: Type]: Type
        ps ← ps.advance  -- skip '['
        let _keyName ← match ps.current.kind with
          | .identifier _ => pure ()
          | _ => throw s!"Expected key name in index signature at line {ps.current.pos.line}"
        ps ← ps.advance
        ps ← ps.expect .colon "Expected ':' after key name in index signature"
        let (ps', _keyType) ← parseTypeExpression ps
        ps := ps'
        ps ← ps.expect .rbracket "Expected ']' in index signature"
        ps ← ps.expect .colon "Expected ':' after ']' in index signature"
        let (ps', valueType) ← parseTypeExpression ps
        ps := ps'
        -- Store as sentinel property since TSInterfaceMember lacks indexSignature variant
        members := members ++ [.property "__index" valueType false isReadonly]
      else
        -- Computed property: [expr]: Type — skip the computed key, parse as regular property
        ps ← ps.advance  -- skip '['
        -- Skip everything until we find ']'
        while !ps.check .rbracket do
          ps ← ps.advance
        ps ← ps.advance  -- skip ']'
        -- Now parse as regular property with a placeholder name
        let optional := ps.check .question
        if optional then
          ps := match ps.advance with | .ok pp => pp | .error _ => ps
        ps ← ps.expect .colon "Expected ':' after computed property name in interface"
        let (ps', ty) ← parseTypeExpression ps
        ps := ps'
        members := members ++ [.property "__computed" ty optional isReadonly]
    else
      let name ← match ps.current.kind with
        | .identifier n => pure n
        | _ => throw s!"Expected member name in interface at line {ps.current.pos.line}"
      ps ← ps.advance
      let optional := ps.check .question
      if optional then
        ps := match ps.advance with | .ok pp => pp | .error _ => ps
      -- Method shorthand: name?<T>(params): ReturnType
      if ps.check .lparen || ps.check .lt then
        let (ps', _typeParams) ← parseTypeParams ps
        ps := ps'
        ps ← ps.expect .lparen "Expected '(' in interface method signature"
        let (ps', params) ← parseFunctionTypeParams ps
        ps := ps'
        ps ← ps.expect .rparen "Expected ')' after interface method parameters"
        let (ps', retTy) ← if ps.check .colon then
          let pa ← ps.advance
          let (pb, ty) ← parseTypeExpression pa
          pure (pb, ty)
        else
          pure (ps, TSType.void_)
        ps := ps'
        members := members ++ [.method name params retTy optional]
      else
        ps ← ps.expect .colon "Expected ':' after interface member name"
        let (ps', ty) ← parseTypeExpression ps
        ps := ps'
        members := members ++ [.property name ty optional isReadonly]
    -- Consume optional semicolon or comma
    if ps.check .semicolon || ps.check .comma then
      ps := match ps.advance with | .ok pp => pp | .error _ => ps
  ps ← ps.expect .rbrace "Expected '}' in interface"
  return (ps, members)

/-- Parse an interface declaration -/
partial def parseTSInterfaceDecl (p : ParserState) :
    ParseResult (ParserState × TSStatement) := do
  let p1 ← p.advance  -- skip 'interface'
  let name ← match p1.current.kind with
    | .identifier n => pure n
    | _ => throw s!"Expected interface name at line {p1.current.pos.line}"
  let p2 ← p1.advance
  let (p3, typeParams) ← parseTypeParams p2
  -- Optional: extends BaseA, BaseB<T>, ...
  let mut ps := p3
  let mut extendsNames : List String := []
  if ps.check .extends then
    ps ← ps.advance
    let mut first := true
    while first || ps.check .comma do
      if !first then
        ps := match ps.advance with | .ok pp => pp | .error _ => ps
      first := false
      let (ps', baseTy) ← parsePrimaryType ps
      ps := ps'
      let baseName := match baseTy with
        | .ref n _ => n
        | _ => "<anonymous>"
      extendsNames := extendsNames ++ [baseName]
  let (p4, members) ← parseInterfaceMembers ps
  return (p4, .interfaceDecl {} name typeParams extendsNames members)

/-- Parse a type alias declaration: type Name = Type; -/
partial def parseTSTypeAliasDecl (p : ParserState) :
    ParseResult (ParserState × TSStatement) := do
  let startPos := p.current.pos
  let p1 ← p.advance  -- skip 'type'
  let name ← match p1.current.kind with
    | .identifier n => pure n
    | _ => throw s!"Expected type name at line {p1.current.pos.line}"
  let p2 ← p1.advance
  let (p3, typeParams) ← parseTypeParams p2
  let p4 ← p3.expect .assign "Expected '=' in type alias"
  -- Allow optional leading pipe: type T = | A | B | C
  let p4' := if p4.check .pipe then
    match p4.advance with | .ok pp => pp | .error _ => p4
  else p4
  let (p5, ty) ← parseTypeExpression p4'
  -- Consume optional semicolon
  let p6 := if p5.check .semicolon then
    match p5.advance with | .ok pp => pp | .error _ => p5
  else p5
  return (p6, .typeAliasDecl (makeBase startPos startPos) name typeParams ty)

/-- Parse an enum declaration: enum Name { Member, Member = value, ... } -/
partial def parseTSEnumDecl (p : ParserState) (isConst : Bool) :
    ParseResult (ParserState × TSStatement) := do
  let p1 ← p.advance  -- skip 'enum'
  let name ← match p1.current.kind with
    | .identifier n => pure n
    | _ => throw s!"Expected enum name at line {p1.current.pos.line}"
  let p2 ← p1.advance
  let p3 ← p2.expect .lbrace "Expected '{' after enum name"
  let mut ps := p3
  let mut members : List TSEnumMember := []
  while !ps.check .rbrace do
    if !members.isEmpty then
      if ps.check .comma then
        ps := match ps.advance with | .ok pp => pp | .error _ => ps
      if ps.check .rbrace then break
    let memberName ← match ps.current.kind with
      | .identifier n => pure n
      | .string s => pure s
      | _ => throw s!"Expected enum member name at line {ps.current.pos.line}"
    ps ← ps.advance
    let (ps', init) ← if ps.check .assign then
      let pa ← ps.advance
      let (pb, expr) ← parseAssignmentExpr pa
      pure (pb, some expr)
    else
      pure (ps, none)
    members := members ++ [{ name := memberName, init }]
    if ps'.check .comma then
      ps := match ps'.advance with | .ok pp => pp | .error _ => ps'
    else
      ps := ps'
  ps ← ps.expect .rbrace "Expected '}' in enum declaration"
  return (ps, .enumDecl {} name members isConst)

/-- Skip an optional semicolon at the current position. -/
private def skipSemicolon (p : ParserState) : ParseResult ParserState :=
  if p.check .semicolon then p.advance else return p

/-- Advance until a semicolon or EOF, consuming the semicolon if present. -/
private partial def skipToSemicolonOrEnd (p : ParserState) : ParseResult ParserState := do
  let mut ps := p
  while !ps.check .semicolon && !ps.atEnd do
    ps ← ps.advance
  if ps.check .semicolon then ps ← ps.advance
  return ps

/-- Parse a brace-enclosed specifier list `{ a, b as c }`, starting at the `{`,
    and consuming the closing `}`. Each entry becomes `⟨imported, local⟩` where
    `local` is the `as` alias when present and the bare name otherwise. Shared by
    named imports and trailing named exports — for `export { local as public }`
    the same shape carries `imported = local`, `localName = public`. `what` names
    the construct for the closing-brace error. -/
private partial def parseBraceSpecifierList (p : ParserState) (what : String) :
    ParseResult (ParserState × List ModuleSpecifier) := do
  let mut ps ← p.advance  -- skip '{'
  let mut specs : List ModuleSpecifier := []
  while !ps.check .rbrace && !ps.atEnd do
    match ps.current.kind with
    | .identifier n =>
      ps ← ps.advance
      let mut localName := n
      if ps.check .as_ then
        ps ← ps.advance  -- skip 'as'
        match ps.current.kind with
        | .identifier a => localName := a; ps ← ps.advance
        | _ => pure ()
      specs := specs ++ [{ imported := n, localName := localName }]
      if ps.check .comma then ps ← ps.advance
    | _ => ps ← ps.advance  -- skip unexpected tokens
  ps ← ps.expect .rbrace s!"Expected '}}' in {what}"
  return (ps, specs)

/-- Parse an ES module import declaration. Handles all four forms, recording the
    written form and per-specifier aliases:
      import { a, b as c } from 'specifier';   (named)
      import DefaultName from 'specifier';      (default)
      import * as NS from 'specifier';          (namespace)
      import 'specifier';                       (side-effect)
    `import type { … }` sets `typeOnly`. -/
partial def parseTSImportDecl (p : ParserState) : ParseResult (ParserState × TSStatement) := do
  let startPos := p.current.pos
  -- Current token is the identifier "import"; advance past it.
  let p0 ← p.advance
  -- Detect `import type { … }`. `type` lexes as the `.type` keyword; treat it as
  -- type-only. (`import type from '…'` — `type` as a default binding — is out of
  -- subset and not distinguished here.)
  let typeOnly := p0.current.kind == .type
  let p1 ← if typeOnly then p0.advance else pure p0
  let base := makeBase startPos startPos
  -- Determine which form we have by looking at the next token.
  match p1.current.kind with
  -- Side-effect import: import 'specifier';
  | .string source =>
    let p2 ← p1.advance
    let p3 ← skipSemicolon p2
    return (p3, .importDecl base source [] .sideEffect false)
  -- Named import: import { a, b as c } from 'specifier';
  | .lbrace =>
    let (p2, specs) ← parseBraceSpecifierList p1 "import specifiers"
    let mut ps := p2
    -- Expect 'from'
    match ps.current.kind with
    | .identifier "from" =>
      ps ← ps.advance
      match ps.current.kind with
      | .string source =>
        ps ← ps.advance
        ps ← skipSemicolon ps
        return (ps, .importDecl base source specs .named typeOnly)
      | _ => throw "Expected string literal after 'from' in import"
    | _ => throw "Expected 'from' after import specifiers"
  -- Namespace import: import * as NS from 'specifier';
  | .star =>
    let mut ps := p1
    ps ← ps.advance  -- skip '*'
    match ps.current.kind with
    | .as_ =>
      ps ← ps.advance  -- skip 'as'
      let nsName := match ps.current.kind with
        | .identifier n => n
        | _ => "_"
      ps ← ps.advance  -- skip namespace name
      match ps.current.kind with
      | .identifier "from" =>
        ps ← ps.advance
        match ps.current.kind with
        | .string source =>
          ps ← ps.advance
          ps ← skipSemicolon ps
          return (ps, .importDecl base source
            [{ imported := nsName, localName := nsName }] .namespaceImport typeOnly)
        | _ => throw "Expected string literal after 'from' in namespace import"
      | _ => throw "Expected 'from' after 'import * as NS'"
    | _ => throw "Expected 'as' after '*' in import"
  -- Default import: import DefaultName from 'specifier';
  | .identifier defName =>
    let mut ps := p1
    ps ← ps.advance  -- skip default name
    match ps.current.kind with
    | .identifier "from" =>
      ps ← ps.advance
      match ps.current.kind with
      | .string source =>
        ps ← ps.advance
        ps ← skipSemicolon ps
        return (ps, .importDecl base source
          [{ imported := defName, localName := defName }] .defaultImport typeOnly)
      | _ => throw "Expected string literal after 'from' in default import"
    | _ => throw "Expected 'from' after default import name"
  | _ =>
    -- Unknown form: skip to semicolon / end
    let p2 ← skipSemicolon p1
    return (p2, .importDecl base "" [] .sideEffect false)

mutual

/-- Parse an ES module export declaration:
      export function f … / export const … / export type … / export interface …  (inline)
      export { a, b as c };                                                       (named)
      export default … / export … from '…' / export *                            (unsupported → routed for rejection)
-/
partial def parseTSExportDecl (p : ParserState) : ParseResult (ParserState × TSStatement) := do
  let startPos := p.current.pos
  let p1 ← p.advance  -- skip 'export'
  let base := makeBase startPos startPos
  match p1.current.kind with
  | .«default» =>            -- export default <decl-or-expr>
    -- Parse the default-exported declaration/expression with the full parser so
    -- a function/class body (with internal semicolons) is consumed correctly,
    -- then discard it — the form is rejected wholesale (TH0089).
    let p2 ← p1.advance      -- skip 'default'
    let (p3, _) ← parseTSStatement p2
    return (p3, .exportUnsupported base .defaultExport)
  | .star =>                 -- export * …  (re-export)
    let p2 ← skipToSemicolonOrEnd p1
    return (p2, .exportUnsupported base .reexport)
  | .lbrace =>
    -- export { a, b as c };  OR  export { a } from '…';  (the latter is a re-export)
    let (ps, specs) ← parseBraceSpecifierList p1 "export specifiers"
    match ps.current.kind with
    | .identifier "from" =>          -- re-export: export { … } from '…'
      let ps2 ← skipToSemicolonOrEnd ps
      return (ps2, .exportUnsupported base .reexport)
    | _ =>
      let ps2 ← skipSemicolon ps
      return (ps2, .exportNamedDecl base specs)
  | _ =>
    -- Inline export on a declaration: parse the inner statement and wrap it.
    let (p2, inner) ← parseTSStatement p1
    return (p2, .exportDecl base inner)

/-- Parse a single TS statement -/
partial def parseTSStatement (p : ParserState) : ParseResult (ParserState × TSStatement) := do
  match p.current.kind with
  | .let | .var =>
    let kind := match p.current.kind with
      | .let => VariableKind.let_
      | _ => VariableKind.var
    parseTSVariableDecl p kind
  | .const =>
    match nextToken p.lexer with
    | .ok (_, tok) =>
      if tok.kind == .enum_ then
        let p1 ← p.advance  -- skip 'const'
        parseTSEnumDecl p1 true
      else
        parseTSVariableDecl p .const
    | .error _ => parseTSVariableDecl p .const
  | .enum_ => parseTSEnumDecl p false
  | .function => parseTSFunctionDecl p
  | .interface => parseTSInterfaceDecl p
  | .type => parseTSTypeAliasDecl p
  | .«declare» =>
    -- declare function/const/class/...
    let p1 ← p.advance
    let (p2, inner) ← parseTSStatement p1
    return (p2, .declareStmt {} inner)
  | .identifier n =>
    if n == "export" then
      parseTSExportDecl p
    else if n == "import" then
      parseTSImportDecl p
    -- `abstract class Foo ...` — consume the `abstract` modifier and parse the
    -- class with its abstract flag set (drives TH0030)
    else if n == "abstract" then
      match p.advance with
      | .ok p1 =>
        if p1.check .class then
          let (p2, stmt) ← parseClassDecl p1 (isAbstract := true)
          return (p2, .js stmt)
        else
          let (p1', stmt) ← parseStatement p
          return (p1', .js stmt)
      | .error _ =>
        let (p1, stmt) ← parseStatement p
        return (p1, .js stmt)
    else
      let (p1, stmt) ← parseStatement p
      return (p1, .js stmt)
  | _ =>
    let (p1, stmt) ← parseStatement p
    return (p1, .js stmt)

end

/-- Parse a TS program (list of TS statements) -/
partial def parseTSProgram (p : ParserState) : ParseResult (ParserState × TSProgram) := do
  let mut ps := p
  let mut stmts : List TSStatement := []
  while !ps.atEnd do
    let (ps', stmt) ← parseTSStatement ps
    ps := ps'
    stmts := stmts ++ [stmt]
  return (ps, { body := stmts })

/-- Parse a string as TypeScript source -/
def parseTSSource (source : String) : Except String TSProgram := do
  let p ← ParserState.init source
  let (p', prog) ← parseTSProgram p
  return { prog with expectErrorDirectives := p'.lexer.directives }

end Thales.Parser
