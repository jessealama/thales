/-
  Thales/AST.lean
  ESTree-compatible AST types for JavaScript

  Reference: https://github.com/estree/estree/blob/master/es5.md
-/

import Thales.TypeCheck.TSType

namespace Thales.AST

open Thales.TypeCheck

/-- Source location information -/
structure Position where
  line : Nat
  column : Nat
  deriving Repr, Inhabited

structure SourceLocation where
  start : Position
  «end» : Position
  deriving Repr, Inhabited

/-- Base node with optional location -/
structure NodeBase where
  loc : Option SourceLocation := none
  deriving Repr, Inhabited

/-- Whether a function carries an `@throws` JSDoc directive, and which types
    were named. The type-checker observes only the constructor (`.absent` ⇒
    "may not throw", `.declared _` ⇒ "may throw"); the emitter destructures
    `.declared types` to build `Except E A`. The `.declared []` case is
    representable but rejected by TH0065 in v1. -/
inductive ThrowsAnnotation where
  | absent
  | declared (types : List String)
  deriving Repr, Inhabited, BEq

/-- Literal values in JavaScript -/
inductive LiteralValue where
  | string (s : String)
  | number (n : Float)
  | boolean (b : Bool)
  | null
  | regex (pattern : String) (flags : String)
  | bigint (value : Int)
  deriving Repr, Inhabited

/-- Identifier -/
structure Identifier where
  base : NodeBase := {}
  name : String
  deriving Repr, Inhabited

/-- Private name (#identifier) -/
structure PrivateName where
  base : NodeBase := {}
  name : String  -- Without the # prefix
  deriving Repr, Inhabited

/-- Variable declaration kind -/
inductive VariableKind where
  | var
  | let_
  | const
  deriving Repr, Inhabited, BEq

/-- Binary operators -/
inductive BinaryOperator where
  | eq      -- ==
  | neq     -- !=
  | seq     -- ===
  | sneq    -- !==
  | lt      -- <
  | leq     -- <=
  | gt      -- >
  | geq     -- >=
  | shl     -- <<
  | shr     -- >>
  | ushr    -- >>>
  | add     -- +
  | sub     -- -
  | mul     -- *
  | div     -- /
  | mod     -- %
  | exp     -- **
  | bitor   -- |
  | bitxor  -- ^
  | bitand  -- &
  | «in»    -- in
  | instanceof
  deriving Repr, Inhabited

/-- Logical operators -/
inductive LogicalOperator where
  | «and»  -- &&
  | «or»   -- ||
  | nullishCoalesce  -- ??
  deriving Repr, Inhabited

/-- Unary operators -/
inductive UnaryOperator where
  | neg     -- -
  | pos     -- +
  | not     -- !
  | bitnot  -- ~
  | typeof
  | void
  | delete
  deriving Repr, Inhabited

/-- Update operators -/
inductive UpdateOperator where
  | inc  -- ++
  | dec  -- --
  deriving Repr, Inhabited

/-- Assignment operators -/
inductive AssignmentOperator where
  | assign     -- =
  | addAssign  -- +=
  | subAssign  -- -=
  | mulAssign  -- *=
  | divAssign  -- /=
  | modAssign  -- %=
  | expAssign  -- **=
  | shlAssign  -- <<=
  | shrAssign  -- >>=
  | ushrAssign -- >>>=
  | orAssign   -- |=
  | xorAssign  -- ^=
  | andAssign  -- &=
  | orLogicalAssign   -- ||=
  | andLogicalAssign  -- &&=
  | nullishAssign     -- ??=
  deriving Repr, Inhabited

/-- Map a compound assignment operator to its underlying binary operator
    (`x OP= y` desugars to `x = x OP y`). `none` for plain `=` and the
    (deferred) logical assignment family. -/
def AssignmentOperator.compoundToBinary : AssignmentOperator → Option BinaryOperator
  | .addAssign  => some .add
  | .subAssign  => some .sub
  | .mulAssign  => some .mul
  | .divAssign  => some .div
  | .modAssign  => some .mod
  | .expAssign  => some .exp
  | .shlAssign  => some .shl
  | .shrAssign  => some .shr
  | .ushrAssign => some .ushr
  | .orAssign   => some .bitor
  | .xorAssign  => some .bitxor
  | .andAssign  => some .bitand
  | _ => none

/-- The short-circuit logical assignment operators (`&&=`, `||=`, `??=`). -/
def AssignmentOperator.isLogical : AssignmentOperator → Bool
  | .orLogicalAssign | .andLogicalAssign | .nullishAssign => true
  | _ => false

/-- Template literal element (string part between interpolations) -/
structure TemplateElement where
  value : String  -- cooked value (escape sequences resolved)
  raw : String    -- raw value (before escape processing)
  tail : Bool     -- whether this is the last element
  deriving Repr, Inhabited

/-- Method kind in class definitions -/
inductive MethodKind where
  | method
  | getter
  | setter
  | constructor
  deriving Inhabited, Repr, BEq

-- Mutually recursive AST types
mutual

/-- Destructuring pattern property for object patterns -/
inductive PatternProperty where
  | mk (base : NodeBase) (key : Expression) (value : Pattern) (computed : Bool) (shorthand : Bool)
  | rest (base : NodeBase) (argument : Pattern)  -- Rest element in object pattern: { ...rest }

/-- Patterns for destructuring binding -/
inductive Pattern where
  | identifier (id : Identifier)
  | objectPattern (base : NodeBase) (properties : List PatternProperty)
  | arrayPattern (base : NodeBase) (elements : List (Option Pattern))
  | assignmentPattern (base : NodeBase) (left : Pattern) (right : Expression)
  | restElement (base : NodeBase) (argument : Pattern)
  | memberPattern (base : NodeBase) (object : Expression) (property : Expression) (computed : Bool)  -- For member expression targets in assignment

/-- Function parameter - can be simple, with default, or rest -/
inductive FunctionParam where
  | simple (id : Identifier)
  | withDefault (id : Identifier) (defaultExpr : Expression)
  | rest (id : Identifier)
  | pattern (pat : Pattern)  -- For destructuring parameters

inductive Property where
  | mk (base : NodeBase) (key : Expression) (value : Expression) (kind : String) (computed : Bool) (shorthand : Bool)

/-- Object property - can be regular property or spread -/
inductive ObjectProperty where
  | regular (base : NodeBase) (key : Expression) (value : Expression)
            (kind : String) (computed : Bool) (shorthand : Bool)
  | spread (base : NodeBase) (argument : Expression)

/-- Method definition in a class -/
inductive MethodDefinition where
  | mk (base : NodeBase) (key : Expression) (value : Expression) (kind : MethodKind) (computed : Bool) (static_ : Bool) (privateName : Option PrivateName := none)

/-- Field definition in a class (instance or static field) -/
inductive FieldDefinition where
  | mk (base : NodeBase) (key : Expression) (value : Option Expression) (computed : Bool) (static_ : Bool) (privateName : Option PrivateName := none)

/-- Class element: either a method, a field definition, or a static block -/
inductive ClassElement where
  | method (def_ : MethodDefinition)
  | field (def_ : FieldDefinition)
  | staticBlock (base : NodeBase) (body : List Statement)

inductive Expression where
  | identifier (base : NodeBase) (name : String)
  | literal (base : NodeBase) (value : LiteralValue) (raw : String)
  | thisExpr (base : NodeBase)
  | arrayExpr (base : NodeBase) (elements : List (Option Expression))
  | objectExpr (base : NodeBase) (properties : List ObjectProperty)
  | functionExpr (base : NodeBase) (id : Option Identifier) (params : List FunctionParam) (body : Statement) (generator : Bool := false) (async : Bool := false)
  | arrowFunctionExpr (base : NodeBase) (params : List FunctionParam) (body : Expression ⊕ Statement) (isExpr : Bool) (async : Bool := false) (returnType : Option TypeAnnotation := none)
  | unaryExpr (base : NodeBase) (operator : UnaryOperator) (isPrefix : Bool) (argument : Expression)
  | updateExpr (base : NodeBase) (operator : UpdateOperator) (argument : Expression) (isPrefix : Bool)
  | binaryExpr (base : NodeBase) (operator : BinaryOperator) (left : Expression) (right : Expression)
  | assignmentExpr (base : NodeBase) (operator : AssignmentOperator) (left : Expression) (right : Expression)
  | logicalExpr (base : NodeBase) (operator : LogicalOperator) (left : Expression) (right : Expression)
  | memberExpr (base : NodeBase) (object : Expression) (property : Expression) (computed : Bool) (optional : Bool := false)
  | privateMemberExpr (base : NodeBase) (object : Expression) (privateName : PrivateName)
  | conditionalExpr (base : NodeBase) (test : Expression) (consequent : Expression) (alternate : Expression)
  | callExpr (base : NodeBase) (callee : Expression) (arguments : List Expression) (optional : Bool := false)
  | newExpr (base : NodeBase) (callee : Expression) (arguments : List Expression)
  | chainExpr (base : NodeBase) (expression : Expression)  -- Wrapper for optional chain
  | sequenceExpr (base : NodeBase) (expressions : List Expression)
  | templateLiteral (base : NodeBase) (quasis : List TemplateElement) (expressions : List Expression)
  | taggedTemplate (base : NodeBase) (tag : Expression) (quasi : Expression)
  | classExpr (base : NodeBase) (id : Option Identifier) (superClass : Option Expression) (body : List ClassElement)
  | super_ (base : NodeBase)  -- super keyword reference (for super.foo and super() detection)
  | spreadElement (base : NodeBase) (argument : Expression)  -- ...expr in arrays/calls
  | yieldExpr (base : NodeBase) (argument : Option Expression) (delegate : Bool)  -- yield / yield*
  | awaitExpr (base : NodeBase) (argument : Expression)  -- await expr
  | patternExpr (base : NodeBase) (pattern : Pattern)  -- Destructuring pattern in assignment context
  | metaProperty (base : NodeBase) («meta» : String) (property : String)  -- new.target

inductive VariableDeclarator where
  | mk (base : NodeBase) (id : Pattern) (init : Option Expression) (typeAnnotation : Option TSType := none)

inductive CatchClause where
  /-- `catch (e: E) { body }` — `catchType` holds the type annotation name (e.g. `"RangeError"`)
      when the catch parameter carries a TS type annotation; `none` means untyped `catch (e)`. -/
  | mk (base : NodeBase) (param : Option Pattern) (body : Statement)
       (catchType : Option String := none)

inductive Statement where
  | emptyStmt (base : NodeBase)
  | blockStmt (base : NodeBase) (body : List Statement)
  | exprStmt (base : NodeBase) (expression : Expression)
  | ifStmt (base : NodeBase) (test : Expression) (consequent : Statement) (alternate : Option Statement)
  | whileStmt (base : NodeBase) (test : Expression) (body : Statement)
  | doWhileStmt (base : NodeBase) (body : Statement) (test : Expression)
  | forStmt (base : NodeBase) (init : Option (Expression ⊕ VariableDeclaration)) (test : Option Expression) (update : Option Expression) (body : Statement)
  | forInStmt (base : NodeBase) (left : Expression ⊕ VariableDeclaration) (right : Expression) (body : Statement)
  | forOfStmt (base : NodeBase) (left : Expression ⊕ VariableDeclaration) (right : Expression) (body : Statement) (await : Bool := false)
  | breakStmt (base : NodeBase) (label : Option Identifier)
  | continueStmt (base : NodeBase) (label : Option Identifier)
  | returnStmt (base : NodeBase) (argument : Option Expression)
  | throwStmt (base : NodeBase) (argument : Expression)
  | tryStmt (base : NodeBase) (block : Statement) (handler : Option CatchClause) (finalizer : Option Statement)
  | switchStmt (base : NodeBase) (discriminant : Expression) (cases : List SwitchCase)
  | labeledStmt (base : NodeBase) (label : Identifier) (body : Statement)
  | withStmt (base : NodeBase) (object : Expression) (body : Statement)
  | debuggerStmt (base : NodeBase)
  | variableDecl (decl : VariableDeclaration)
  | functionDecl (base : NodeBase) (id : Identifier) (params : List FunctionParam) (body : Statement) (generator : Bool := false) (async : Bool := false)
  | classDecl (base : NodeBase) (id : Identifier) (superClass : Option Expression) (body : List ClassElement)

inductive VariableDeclaration where
  | mk (base : NodeBase) (declarations : List VariableDeclarator) (kind : VariableKind)

inductive SwitchCase where
  | mk (base : NodeBase) (test : Option Expression) (consequent : List Statement)

end

/-- Source location of an expression — the `loc` field of its `NodeBase`.
    Every `Expression` constructor carries a `NodeBase` as its first field,
    so this is exhaustive and total. -/
def exprLoc : Expression → Option SourceLocation
  | .identifier         base _         => base.loc
  | .literal            base _ _       => base.loc
  | .thisExpr           base           => base.loc
  | .arrayExpr          base _         => base.loc
  | .objectExpr         base _         => base.loc
  | .functionExpr       base _ _ _ _ _ => base.loc
  | .arrowFunctionExpr  base _ _ _ _ _ => base.loc
  | .unaryExpr          base _ _ _     => base.loc
  | .updateExpr         base _ _ _     => base.loc
  | .binaryExpr         base _ _ _     => base.loc
  | .assignmentExpr     base _ _ _     => base.loc
  | .logicalExpr        base _ _ _     => base.loc
  | .memberExpr         base _ _ _ _   => base.loc
  | .privateMemberExpr  base _ _       => base.loc
  | .conditionalExpr    base _ _ _     => base.loc
  | .callExpr           base _ _ _     => base.loc
  | .newExpr            base _ _       => base.loc
  | .chainExpr          base _         => base.loc
  | .sequenceExpr       base _         => base.loc
  | .templateLiteral    base _ _       => base.loc
  | .taggedTemplate     base _ _       => base.loc
  | .classExpr          base _ _ _     => base.loc
  | .super_             base           => base.loc
  | .spreadElement      base _         => base.loc
  | .yieldExpr          base _ _       => base.loc
  | .awaitExpr          base _         => base.loc
  | .patternExpr        base _         => base.loc
  | .metaProperty       base _ _       => base.loc

-- Manual Inhabited instances for mutual types
mutual

partial def Pattern.default : Pattern :=
  .identifier { name := "" }

partial def PatternProperty.default : PatternProperty :=
  .mk {} Expression.default Pattern.default false false

partial def FunctionParam.default : FunctionParam :=
  .simple { name := "" }

partial def Expression.default : Expression :=
  .identifier {} ""

partial def Statement.default : Statement :=
  .emptyStmt {}

partial def Property.default : Property :=
  .mk {} Expression.default Expression.default "init" false false

partial def ObjectProperty.default : ObjectProperty :=
  .regular {} Expression.default Expression.default "init" false false

partial def MethodDefinition.default : MethodDefinition :=
  .mk {} Expression.default Expression.default .method false false

partial def FieldDefinition.default : FieldDefinition :=
  .mk {} Expression.default none false false

partial def ClassElement.default : ClassElement :=
  .method MethodDefinition.default

partial def VariableDeclarator.default : VariableDeclarator :=
  .mk {} Pattern.default none none

partial def CatchClause.default : CatchClause :=
  .mk {} Pattern.default Statement.default none

partial def VariableDeclaration.default : VariableDeclaration :=
  .mk {} [] .var

partial def SwitchCase.default : SwitchCase :=
  .mk {} none []

end

instance : Inhabited Pattern := ⟨Pattern.default⟩
instance : Inhabited PatternProperty := ⟨PatternProperty.default⟩
instance : Inhabited FunctionParam := ⟨FunctionParam.default⟩
instance : Inhabited Expression := ⟨Expression.default⟩
instance : Inhabited Statement := ⟨Statement.default⟩
instance : Inhabited Property := ⟨Property.default⟩
instance : Inhabited ObjectProperty := ⟨ObjectProperty.default⟩
instance : Inhabited MethodDefinition := ⟨MethodDefinition.default⟩
instance : Inhabited FieldDefinition := ⟨FieldDefinition.default⟩
instance : Inhabited ClassElement := ⟨ClassElement.default⟩
instance : Inhabited VariableDeclarator := ⟨VariableDeclarator.default⟩
instance : Inhabited CatchClause := ⟨CatchClause.default⟩
instance : Inhabited VariableDeclaration := ⟨VariableDeclaration.default⟩
instance : Inhabited SwitchCase := ⟨SwitchCase.default⟩

/-- Program node (top-level) -/
structure Program where
  base : NodeBase := {}
  body : List Statement
  sourceType : String := "script"
  deriving Inhabited

end Thales.AST
