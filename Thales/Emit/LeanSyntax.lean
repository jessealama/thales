/-
  Thales/Emit/LeanSyntax.lean
  A compact AST for the Lean source we emit, plus a pretty printer.
  Deliberately minimal — only what v1 emits.
-/
namespace Thales.Emit.LeanSyntax

/-- Lean type expression. -/
inductive LType where
  | var (name : String)                        -- α, β
  | const (name : String)                      -- Float, Int, String, Bool, Unit
  | app (head : String) (args : List LType)    -- Array α, Option T, Foo α β
  | arrow (from_ : LType) (to_ : LType)        -- α → β
  | prod (left : LType) (right : LType)        -- α × β
  | sum (left : LType) (right : LType)         -- α ⊕ β (right-associative for union chains)
  -- A placeholder that renders to nothing and tells the printer to omit
  -- the `: T` annotation entirely. Used at top-level `def` sites where the
  -- type is fully inferable from the body (e.g. `const bit = asBit(1)`).
  | inferred
  deriving Inhabited

/-- Lean pattern (for match arms). -/
inductive LPattern where
  | wildcard                                    -- _
  | var (name : String)                         -- r
  | ctor (name : String) (args : List LPattern) -- .circle r
  deriving Inhabited

mutual

/-- Lean term. Only the subset the emitter uses. -/
inductive LExpr where
  | var (name : String)
  | int (n : Int)
  | float (n : Float)
  | str (s : String)
  | bool (b : Bool)
  | app (fn : LExpr) (args : List LExpr)
  | lam (params : List (String × Option LType)) (body : LExpr)
  | letE (name : String) (ty : Option LType) (value body : LExpr)
  | match_ (scrutinee : LExpr) (arms : List (LPattern × LExpr))
  | ite (cond thn els : LExpr)
  | binOp (op : String) (l r : LExpr)
  | ctor (name : String) (args : List LExpr)    -- .circle 1.0
  | proj (obj : LExpr) (field : String)         -- p.x
  | structLit (typeName : String) (fields : List (String × LExpr)) -- { x := 1, y := 2 }
  -- Anonymous constructor `⟨e₁, …, eₙ⟩` plus a trailing tactic-script proof.
  -- Used to build refinement-typed Subtype values: `⟨42.0, by native_decide⟩`,
  -- `⟨x, h⟩`, etc. `proofTactic` is rendered verbatim after the comma —
  -- callers supply complete tactic syntax (e.g. `"by native_decide"`,
  -- `"h"`).
  | anonCtor (args : List LExpr) (proofTactic : String)
  -- Optional indexing: `arr[k]?` returning `Option α`. Used as the P0
  -- fallback when no bounds proof is available.
  | indexOpt (arr : LExpr) (idx : LExpr)
  -- Dependent if-then-else: `if h : c then t else e`. Used to bind a
  -- proof of the condition into the then-branch so refinement-typed
  -- accessors can discharge their bounds proofs.
  | dite_ (binderName : String) (cond thn els : LExpr)
  -- A `do`-block sequencing several IO actions: `(do s₁; s₂; …)`. Used to
  -- sequence top-level IO statements (e.g. two consecutive `console.log`s
  -- inside an `if` branch) where there is no value to bind.
  -- MUST be constructed with ≥ 2 elements: empty renders invalid `(do)` and
  -- a singleton is degenerate. All current call sites are guarded by
  -- `stmtsHaveIO`, which ensures the tail is non-empty before wrapping.
  | doSeq (stmts : List LExpr)
  -- An `Id.run do` block with mutable locals (#24). MUST be constructed
  -- with ≥ 1 statement, and every control path through the statements must
  -- end in a `ret` (the emitter guarantees this; a fall-through path would
  -- render a do-block with no value).
  | idRunDo (stmts : List LDoStmt)
  -- Integer range `[0:n]` for `for` loops (#25). Renders as `[0:{n}]`.
  -- Bracket-delimited, so atomic — renderExprAtom must NOT wrap it in parens.
  | rangeTo (stop : LExpr)

/-- A statement inside an `Id.run do` block (#24). Only what do-mode
    emission needs: mutable/immutable lets, reassignment, early return,
    statement-position `if`, `match` with statement-list arms, and for
    loops with break/continue (#25). -/
inductive LDoStmt where
  | letMut (name : String) (ty : Option LType) (value : LExpr)   -- let mut n := e
  | letPure (name : String) (ty : Option LType) (value : LExpr)  -- let n := e
  | assign (name : String) (value : LExpr)                       -- n := e
  | ret (value : LExpr)                                          -- return e
  -- `if c then …` / `if c then … else …`; an empty branch renders `pure ()`
  | ifDo (cond : LExpr) (thn : List LDoStmt) (els : List LDoStmt)
  | matchDo (scrutinee : LExpr) (arms : List (LPattern × List LDoStmt))
  -- `for v in iter do …` (#25); may run zero iterations, so not terminating
  | forDo (var : String) (iter : LExpr) (body : List LDoStmt)
  | breakDo                                                       -- break
  | continueDo                                                    -- continue

end

instance : Inhabited LExpr := ⟨.var ""⟩
instance : Inhabited LDoStmt := ⟨.ret (.var "")⟩

/-- Whether a do-statement list `return`s on every control path — i.e. an
    `idRunDo` built from it never falls off the end. Conservative (false
    when unsure). -/
partial def doStmtsTerminate (stmts : List LDoStmt) : Bool :=
  match stmts.getLast? with
  | none => false
  | some (.ret _) => true
  | some (.ifDo _ thn els) =>
      !els.isEmpty && doStmtsTerminate thn && doStmtsTerminate els
  | some (.matchDo _ arms) =>
      !arms.isEmpty && arms.all fun (_, ss) => doStmtsTerminate ss
  -- Deliberately covers letMut/letPure/assign/forDo/breakDo/continueDo.
  -- forDo may run zero iterations and so is never itself terminating (#25).
  | some _ => false

/-- Top-level declaration. -/
inductive LDecl where
  | def_ (name : String)
         (typeParams : List String)
         (params : List (String × LType))
         (retTy : LType)
         (body : LExpr)
         (isPartial : Bool := false)  -- emit as `partial def` when true
  | struct (name : String)
           (typeParams : List String)
           (fields : List (String × LType))
  | inductive_ (name : String)
               (typeParams : List String)
               (ctors : List (String × List (String × LType)))
  | abbrev_ (name : String) (typeParams : List String) (ty : LType)
  | namespace_ (name : String) (body : List LDecl)
  -- `#eval <expr>` — a top-level elaboration-time effect. Used for
  -- translating top-level `console.log(...)` calls into Lean output.
  | eval_ (expr : LExpr)
  -- An anonymous typeclass instance: `instance : <classApp> where <field> := <body>`.
  -- Used for emitting Coe and similar single-method instances.
  | instance_ (classApp : LType)
              (fieldName : String)
              (body : LExpr)
  deriving Inhabited

/-- A pretty-printed Lean module. -/
structure LModule where
  imports : List String          -- ["Thales.TS.Runtime"]
  opens : List String            -- ["Thales.TS"]
  decls : List LDecl
  deriving Inhabited

/-! ### Pretty printer -/

/-- Concatenate with newlines. -/
private def lines (xs : List String) : String :=
  String.intercalate "\n" xs

/-- Indent every non-empty line by two spaces. -/
private def indent (s : String) : String :=
  let ls := s.splitOn "\n"
  String.intercalate "\n" (ls.map fun l => if l.isEmpty then l else "  " ++ l)

/-- Escape backslashes and double-quotes in a string literal. -/
private def escapeString (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\"" "\\\""

/-- Render a float so Lean parses it as a Float literal.
    Ensures a decimal point is present. -/
private def renderFloat (f : Float) : String :=
  let s := toString f
  if s.contains '.' || s.contains 'e' || s.contains 'E' then s
  else s ++ ".0"

/-- Render type params as `{α : Type} {β : Type}` (implicit binders). -/
private def renderTypeParams (ps : List String) : String :=
  if ps.isEmpty then ""
  else " " ++ String.intercalate " " (ps.map fun p => "{" ++ p ++ " : Type}")

mutual

  partial def renderType : LType → String
    | .var n    => n
    | .const n  => n
    | .app head [] => head
    | .app head args =>
        s!"({head} {String.intercalate " " (args.map renderTypeAtom)})"
    | .arrow f t => s!"({renderType f} → {renderType t})"
    | .prod l r  => s!"({renderType l} × {renderType r})"
    | .sum l r   => s!"{renderTypeAtom l} ⊕ {renderType r}"
    | .inferred  => "_"

  partial def renderTypeAtom : LType → String
    | .var n   => n
    | .const n => n
    | other    => s!"({renderType other})"

end

mutual

  partial def renderPattern : LPattern → String
    | .wildcard      => "_"
    | .var n         => n
    | .ctor n []     => s!".{n}"
    | .ctor n args   =>
        s!".{n} {String.intercalate " " (args.map renderPatternAtom)}"

  partial def renderPatternAtom : LPattern → String
    | .wildcard    => "_"
    | .var n       => n
    | .ctor n []   => s!".{n}"
    | .ctor n args =>
        s!"(.{n} {String.intercalate " " (args.map renderPatternAtom)})"

end

mutual

  partial def renderExpr : LExpr → String
    | .var n    => n
    | .int n    => if n < 0 then s!"({n})" else toString n
    | .float f  => renderFloat f
    | .str s    => s!"\"{escapeString s}\""
    | .bool true  => "true"
    | .bool false => "false"
    | .app fn args =>
        let parts := renderExprAtom fn :: args.map renderExprAtom
        s!"({String.intercalate " " parts})"
    | .lam params body =>
        let ps := params.map fun (n, tOpt) =>
          match tOpt with
          | some t => s!"({n} : {renderType t})"
          | none   => n
        s!"(fun {String.intercalate " " ps} => {renderExpr body})"
    | .letE n tOpt v b =>
        let annot := match tOpt with
          | some t => s!" : {renderType t}"
          | none   => ""
        s!"let {n}{annot} := {renderExpr v}\n{renderExpr b}"
    | .match_ scrut arms =>
        let armsS := arms.map fun (p, e) =>
          s!"| {renderPattern p} => {renderExpr e}"
        s!"match {renderExpr scrut} with\n{indent (lines armsS)}"
    | .ite c t e =>
        s!"if {renderExpr c} then {renderExpr t} else {renderExpr e}"
    | .binOp op l r =>
        s!"({renderExpr l} {op} {renderExpr r})"
    | .ctor n [] => s!".{n}"
    | .ctor n args =>
        s!"(.{n} {String.intercalate " " (args.map renderExprAtom)})"
    | .proj obj field =>
        s!"{renderExprAtom obj}.{field}"
    | .structLit typeName fields =>
        let fieldS := fields.map fun (n, e) => s!"{n} := {renderExpr e}"
        s!"(\{ {String.intercalate ", " fieldS} : {typeName} })"
    | .anonCtor args proofTactic =>
        let argsS := args.map renderExpr
        let parts := argsS ++ [proofTactic]
        s!"⟨{String.intercalate ", " parts}⟩"
    | .indexOpt arr idx =>
        s!"{renderExprAtom arr}[{renderExpr idx}]?"
    | .dite_ binderName cond thn els =>
        s!"if {binderName} : {renderExpr cond} then {renderExpr thn} else {renderExpr els}"
    | .doSeq stmts =>
        -- Each statement must render as a SINGLE `do`-element. A `letE`/`dite_`/
        -- `ite`/`match_` element produces a multi-line `let …; … else …` chain
        -- whose layout would otherwise leak into the whitespace-sensitive `do`
        -- block and orphan a trailing `else`. `renderExprAtom` parenthesizes any
        -- non-atomic element, keeping the chain (and its `else`) grouped; bare
        -- `app`s like `consoleLog x` are wrapped harmlessly as `(consoleLog x)`.
        let body := lines (stmts.map renderExprAtom)
        s!"(do\n{indent body})"
    | .idRunDo stmts =>
        s!"Id.run do\n{indent (renderDoStmts stmts)}"
    | .rangeTo stop =>
        s!"[0:{renderExpr stop}]"

  /-- Render a do-statement list; an empty list renders `pure ()` so empty
      `if` branches stay valid Lean. -/
  partial def renderDoStmts (stmts : List LDoStmt) : String :=
    if stmts.isEmpty then "pure ()" else lines (stmts.map renderDoStmt)

  partial def renderDoStmt : LDoStmt → String
    | .letMut n tyOpt v =>
        let annot := match tyOpt with
          | some t => s!" : {renderType t}"
          | none   => ""
        s!"let mut {n}{annot} := {renderExpr v}"
    | .letPure n tyOpt v =>
        let annot := match tyOpt with
          | some t => s!" : {renderType t}"
          | none   => ""
        s!"let {n}{annot} := {renderExpr v}"
    | .assign n v => s!"{n} := {renderExpr v}"
    | .ret v => s!"return {renderExpr v}"
    | .ifDo c thn [] =>
        s!"if {renderExpr c} then\n{indent (renderDoStmts thn)}"
    | .ifDo c thn els =>
        s!"if {renderExpr c} then\n{indent (renderDoStmts thn)}\nelse\n{indent (renderDoStmts els)}"
    | .matchDo scrut arms =>
        let armsS := arms.map fun (p, stmts) =>
          s!"| {renderPattern p} =>\n{indent (renderDoStmts stmts)}"
        s!"match {renderExpr scrut} with\n{lines armsS}"
    | .forDo var iter body =>
        s!"for {var} in {renderExpr iter} do\n{indent (renderDoStmts body)}"
    | .breakDo    => "break"
    | .continueDo => "continue"

  partial def renderExprAtom : LExpr → String
    | .var n      => n
    | .int n      => if n < 0 then s!"({n})" else toString n
    | .float f    => renderFloat f
    | .str s      => s!"\"{escapeString s}\""
    | .bool true  => "true"
    | .bool false => "false"
    | .ctor n []  => s!".{n}"
    | .proj obj field => s!"{renderExprAtom obj}.{field}"
    -- rangeTo is bracket-delimited and therefore atomic; no extra parens
    | .rangeTo stop => s!"[0:{renderExpr stop}]"
    | other       => s!"({renderExpr other})"

end

partial def renderDecl : LDecl → String
  | .def_ name tps params retTy body isPartial =>
      let tpsS    := renderTypeParams tps
      let paramsS := params.map fun (n, t) => s!"({n} : {renderType t})"
      let paramsLine :=
        if paramsS.isEmpty then "" else " " ++ String.intercalate " " paramsS
      let keyword := if isPartial then "partial def" else "def"
      let retAnnot := match retTy with
        | .inferred => ""
        | other => s!" : {renderType other}"
      s!"{keyword} {name}{tpsS}{paramsLine}{retAnnot} :=\n{indent (renderExpr body)}"
  | .struct name tps fields =>
      let tpsS       := renderTypeParams tps
      let fieldLines := fields.map fun (n, t) => s!"{n} : {renderType t}"
      s!"structure {name}{tpsS} where\n{indent (lines fieldLines)}\n  deriving Repr, BEq"
  | .inductive_ name tps ctors =>
      let tpsS     := renderTypeParams tps
      let ctorLines := ctors.map fun (ctorName, fields) =>
        if fields.isEmpty then s!"| {ctorName}"
        else
          let fieldS := fields.map fun (fn, ft) => s!"({fn} : {renderType ft})"
          s!"| {ctorName} {String.intercalate " " fieldS}"
      s!"inductive {name}{tpsS} where\n{indent (lines ctorLines)}\n  deriving Repr"
  | .abbrev_ name tps ty =>
      let tpsS := renderTypeParams tps
      s!"abbrev {name}{tpsS} := {renderType ty}"
  | .namespace_ name body =>
      let inner := body.map renderDecl
      s!"namespace {name}\n\n{String.intercalate "\n\n" inner}\n\nend {name}"
  | .eval_ expr =>
      s!"#eval {renderExpr expr}"
  | .instance_ classApp fieldName body =>
      s!"instance : {renderType classApp} where\n  {fieldName} := {renderExpr body}"

/-- Render a complete Lean module to a source string. -/
def renderModule (m : LModule) : String :=
  let importLines := m.imports.map fun i => s!"import {i}"
  let openLines   := m.opens.map   fun o => s!"open {o}"
  -- Generated code can leave parameters unused (e.g. a generic `<A, B>(a, b)`
  -- function that only returns `a`); silence the linter so emitted Lean
  -- elaborates without warning noise in golden output comparisons.
  let preambleLines := ["set_option linter.unusedVariables false"]
  let declLines := m.decls.map renderDecl
  let parts : List String :=
    (if importLines.isEmpty then [] else [lines importLines]) ++
    (if openLines.isEmpty   then [] else [lines openLines])   ++
    [lines preambleLines] ++
    declLines
  String.intercalate "\n\n" parts ++ "\n"

end Thales.Emit.LeanSyntax
