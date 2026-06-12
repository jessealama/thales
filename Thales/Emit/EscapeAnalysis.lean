/-
  Thales/Emit/EscapeAnalysis.lean
  Per-function mutation-eligibility analysis (issue #24).
  A binding is mutable-eligible iff every reference to it (read or write)
  occurs in the declaring function's own body — no reference from any
  nested function/arrow. Conservative on several axes, all safe (they only
  reject, never accept):
    * any identifier occurrence inside a nested function counts as a
      capture, even if the inner function shadows the name;
    * a mutated variable that is null/undefined-tested or appears as the
      sole argument of a call in an `if`/ternary condition (the
      refinement-predicate shape) is ineligible — assignment would
      invalidate narrowing evidence the emitter bakes into `dite`/`match`.
  Beyond per-variable eligibility, `doModeLowerable` is the function-level
  gate (#25/#40/#41): bodies containing a `try`/`catch`, a switch shape the
  do-mode emitter cannot lower, a loop shape the do-mode emitter cannot
  lower, or a read of a narrow-tested variable outside its test positions
  stay on the pure emission path entirely, so their mutation is rejected
  wholesale.
-/
import Thales.AST
import Thales.Emit.LoopShape
import Std.Data.HashSet

namespace Thales.Emit.EscapeAnalysis

open Thales.AST

structure MutationInfo where
  /-- Identifier targets of assignment/update anywhere in the own body. -/
  mutated : Std.HashSet String := {}
  /-- Identifiers occurring anywhere inside a nested function/arrow. -/
  capturedRefs : Std.HashSet String := {}
  /-- `let`/`var` names declared WITH an initializer in the own body. -/
  initializedLets : Std.HashSet String := {}
  /-- `let`/`var` names declared WITHOUT an initializer. -/
  uninitializedLets : Std.HashSet String := {}
  /-- `const` names declared in the own body (mutation of these is tsc's
      TS2588 territory — no TH code on top). -/
  consts : Std.HashSet String := {}
  /-- Parameter names. -/
  params : Std.HashSet String := {}
  /-- Vars null/undefined-tested or refinement-predicate-tested in a
      condition. -/
  narrowTested : Std.HashSet String := {}
  /-- Identifiers referenced in the own body outside narrow-test positions:
      the subject occurrence of `x === null` / `pred(x)` does not count,
      every other occurrence does. Mutation targets are not references. -/
  nonTestRefs : Std.HashSet String := {}
  /-- The own body contains a `switch` that do-mode cannot lower: an arm
      that does not return on every path (`break`-style fall-through would
      need post-switch join emission), a `default` arm, or a scrutinee that
      is not the `ident.field` shape of a discriminated-union dispatch.
      Mutation in such a function stays rejected. -/
  hasUnloweredSwitchShape : Bool := false
  /-- The own body contains a `try`/`catch` (#41): the exception path emits
      pure Except match-chains, which do-mode cannot thread through, so
      mutation in such a function stays rejected. -/
  hasTryShape : Bool := false
  /-- The own body contains a loop `classifyLoop` admits (#25). Triggers
      do-mode entry even without eligible mutation — the pure path cannot
      host a loop. -/
  hasLowerableLoop : Bool := false
  /-- The own body contains a loop do-mode cannot lower: `notLowerable`
      shape, a loop variable that is reassigned, a canonical-for bound
      identifier that is reassigned, or a labeled break/continue. Poisons
      do-mode wholesale, like `hasTryShape`. -/
  hasUnloweredLoopShape : Bool := false

def MutationInfo.eligible (info : MutationInfo) (name : String) : Bool :=
  (info.params.contains name || info.initializedLets.contains name)
    && !info.capturedRefs.contains name
    && !info.narrowTested.contains name

/-- A narrow-tested variable is referenced outside its test positions —
    in the own body or from a nested function (#40). The pure path bakes
    such narrowing into `dite`/`match` rebinding; do-mode's plain `if`
    carries no evidence, so the read would elaborate at the unnarrowed
    type. Such a function must stay on the pure emission path. -/
def MutationInfo.narrowingDependentBody (info : MutationInfo) : Bool :=
  info.narrowTested.toList.any fun n =>
    info.nonTestRefs.contains n || info.capturedRefs.contains n

/-- Function-level do-mode admissibility (#25/#40/#41): the single predicate
    that BOTH SubsetCheck's mutation routing and `emitFuncDecl`'s do-mode
    entry consult — they must never disagree, or accepted programs get
    miscompiled. False when the body contains a shape `emitBodyDo` cannot
    lower (unlowered switch, try/catch, unlowered loop, or narrowing-dependent
    body). -/
def MutationInfo.doModeLowerable (info : MutationInfo) : Bool :=
  !info.hasUnloweredSwitchShape && !info.hasTryShape
    && !info.narrowingDependentBody && !info.hasUnloweredLoopShape

private def insertAll (s : Std.HashSet String) (xs : List String) : Std.HashSet String :=
  xs.foldl (·.insert ·) s

/- All identifiers in an expression/statement, including inside nested
   function bodies. Used to account a nested function's references
   wholesale to `capturedRefs`. -/
mutual
partial def identsExpr : Expression → List String
  | .identifier _ n => [n]
  | .literal _ _ _ | .thisExpr _ | .super_ _ | .metaProperty _ _ _
  | .patternExpr _ _ => []
  | .arrayExpr _ els =>
      els.flatMap fun | some e => identsExpr e | none => []
  | .objectExpr _ props => props.flatMap fun
      | .regular _ k v _ _ _ => identsExpr k ++ identsExpr v
      | .spread _ a => identsExpr a
  | .functionExpr _ _ _ body _ _ => identsStmt body
  | .arrowFunctionExpr _ _ body _ _ _ =>
      match body with | .inl e => identsExpr e | .inr s => identsStmt s
  | .unaryExpr _ _ _ a | .updateExpr _ _ a _ | .spreadElement _ a
  | .awaitExpr _ a | .chainExpr _ a => identsExpr a
  | .binaryExpr _ _ l r | .assignmentExpr _ _ l r | .logicalExpr _ _ l r =>
      identsExpr l ++ identsExpr r
  | .memberExpr _ o p _ _ => identsExpr o ++ identsExpr p
  | .privateMemberExpr _ o _ => identsExpr o
  | .conditionalExpr _ t c a => identsExpr t ++ identsExpr c ++ identsExpr a
  | .callExpr _ f args _ | .newExpr _ f args =>
      identsExpr f ++ args.flatMap identsExpr
  | .sequenceExpr _ es => es.flatMap identsExpr
  | .templateLiteral _ _ es => es.flatMap identsExpr
  | .taggedTemplate _ t q => identsExpr t ++ identsExpr q
  | .classExpr _ _ _ _ => []   -- classes are TH0030-rejected; don't dig
  | .yieldExpr _ a _ => match a with | some e => identsExpr e | none => []

partial def identsStmt : Statement → List String
  | .exprStmt _ e | .throwStmt _ e => identsExpr e
  | .blockStmt _ b => b.flatMap identsStmt
  | .ifStmt _ t c a =>
      identsExpr t ++ identsStmt c
        ++ (match a with | some s => identsStmt s | none => [])
  | .returnStmt _ a => match a with | some e => identsExpr e | none => []
  | .variableDecl (.mk _ decls _) =>
      decls.flatMap fun (.mk _ _ init _) =>
        match init with | some e => identsExpr e | none => []
  | .whileStmt _ t b => identsExpr t ++ identsStmt b
  | .doWhileStmt _ b t => identsStmt b ++ identsExpr t
  | .forStmt _ init t u b =>
      (match init with
        | some (.inl e) => identsExpr e
        | some (.inr (.mk _ decls _)) =>
            decls.flatMap fun (.mk _ _ i _) =>
              match i with | some e => identsExpr e | none => []
        | none => [])
        ++ (match t with | some e => identsExpr e | none => [])
        ++ (match u with | some e => identsExpr e | none => [])
        ++ identsStmt b
  | .forInStmt _ left r b | .forOfStmt _ left r b _ =>
      (match left with | .inl e => identsExpr e | .inr _ => [])
        ++ identsExpr r ++ identsStmt b
  | .switchStmt _ d cases =>
      identsExpr d ++ cases.flatMap (fun (.mk _ t ss) =>
        (match t with | some e => identsExpr e | none => [])
          ++ ss.flatMap identsStmt)
  | .tryStmt _ b h f =>
      identsStmt b
        ++ (match h with | some (.mk _ _ hb _) => identsStmt hb | none => [])
        ++ (match f with | some s => identsStmt s | none => [])
  | .labeledStmt _ _ b | .withStmt _ _ b => identsStmt b
  | .functionDecl _ _ _ b _ _ => identsStmt b
  | _ => []
end

/-- Whether a statement list returns or throws on every control path.
    Conservative (false when unsure); the do-mode twin of the checker's
    `alwaysReturns`. -/
partial def stmtsReturn (stmts : List Statement) : Bool :=
  stmts.any fun s =>
    match s with
    | .returnStmt _ _ => true
    | .throwStmt _ _ => true
    | .blockStmt _ ss => stmtsReturn ss
    | .ifStmt _ _ c (some a) => stmtsReturn [c] && stmtsReturn [a]
    | _ => false

/-- A nullish test operand: the `null` literal or the `undefined`
    identifier (`undefined` is an identifier in the AST, not a literal). -/
private def isNullishOperand : Expression → Bool
  | .literal _ .null _ => true
  | .identifier _ "undefined" => true
  | _ => false

/- Walk the function's OWN body: nested functions are not descended into —
   every identifier they mention lands in `capturedRefs` wholesale. -/
mutual
partial def walkExpr (acc : MutationInfo) : Expression → MutationInfo
  | .identifier _ n =>
      { acc with nonTestRefs := acc.nonTestRefs.insert n }
  | .assignmentExpr _ _ (.identifier _ n) r =>
      walkExpr { acc with mutated := acc.mutated.insert n } r
  | .assignmentExpr _ _ l r => walkExpr (walkExpr acc l) r
  | .updateExpr _ _ (.identifier _ n) _ =>
      { acc with mutated := acc.mutated.insert n }
  | .updateExpr _ _ a _ => walkExpr acc a
  | .functionExpr _ _ _ body _ _ =>
      { acc with capturedRefs := insertAll acc.capturedRefs (identsStmt body) }
  | .arrowFunctionExpr _ _ body _ _ _ =>
      let ids := match body with | .inl e => identsExpr e | .inr s => identsStmt s
      { acc with capturedRefs := insertAll acc.capturedRefs ids }
  | .conditionalExpr _ t c a =>
      walkExpr (walkExpr (walkCond acc t) c) a
  | .unaryExpr _ _ _ a | .spreadElement _ a | .awaitExpr _ a | .chainExpr _ a =>
      walkExpr acc a
  | .binaryExpr _ _ l r | .logicalExpr _ _ l r =>
      walkExpr (walkExpr acc l) r
  | .memberExpr _ o p _ _ => walkExpr (walkExpr acc o) p
  | .privateMemberExpr _ o _ => walkExpr acc o
  | .callExpr _ f args _ | .newExpr _ f args =>
      args.foldl walkExpr (walkExpr acc f)
  | .arrayExpr _ els =>
      els.foldl (fun a oe => match oe with | some e => walkExpr a e | none => a) acc
  | .objectExpr _ props =>
      props.foldl (fun a p => match p with
        | .regular _ k v _ _ _ => walkExpr (walkExpr a k) v
        | .spread _ s => walkExpr a s) acc
  | .sequenceExpr _ es | .templateLiteral _ _ es => es.foldl walkExpr acc
  | .taggedTemplate _ t q => walkExpr (walkExpr acc t) q
  | .yieldExpr _ a _ => match a with | some e => walkExpr acc e | none => acc
  | _ => acc

/-- Walk an `if`/ternary condition. The narrow-test shapes — nullish
    equality (`===`/`!==`/`==`/`!=` against `null`/`undefined`, either
    operand order) and the single-ident-argument predicate call — mark
    their subject in `narrowTested` WITHOUT recording that occurrence in
    `nonTestRefs`; every other subtree walks normally. Must stay a
    superset of the shapes the emitter bakes narrowing for
    (`nullCheckVar`, `detectRefinementPredicate`). -/
partial def walkCond (acc : MutationInfo) : Expression → MutationInfo
  | e@(.binaryExpr _ op l r) =>
      let nullishEqOp := match op with
        | .seq | .sneq | .eq | .neq => true
        | _ => false
      let subjectOf : Expression → Expression → Option String := fun a b =>
        match a with
        | .identifier _ n =>
            if isNullishOperand b && n != "undefined" then some n else none
        | _ => none
      if nullishEqOp then
        match subjectOf l r <|> subjectOf r l with
        | some n => { acc with narrowTested := acc.narrowTested.insert n }
        | none => walkExpr acc e
      else
        walkExpr acc e
  | .callExpr _ f [.identifier _ n] _ =>
      walkExpr { acc with narrowTested := acc.narrowTested.insert n } f
  | .unaryExpr _ .not _ a => walkCond acc a
  | .logicalExpr _ _ l r => walkCond (walkCond acc l) r
  | e => walkExpr acc e

partial def walkStmt (acc : MutationInfo) : Statement → MutationInfo
  | .exprStmt _ e | .throwStmt _ e => walkExpr acc e
  | .blockStmt _ b => b.foldl walkStmt acc
  | .ifStmt _ t c a =>
      let acc := walkStmt (walkCond acc t) c
      match a with | some s => walkStmt acc s | none => acc
  | .returnStmt _ a => match a with | some e => walkExpr acc e | none => acc
  | .variableDecl (.mk _ decls kind) =>
      decls.foldl (fun a (.mk _ pat init _) =>
        let a := match init with | some e => walkExpr a e | none => a
        match pat with
        | .identifier id =>
          if kind == .const then { a with consts := a.consts.insert id.name }
          else match init with
            | some _ => { a with initializedLets := a.initializedLets.insert id.name }
            | none => { a with uninitializedLets := a.uninitializedLets.insert id.name }
        | _ => a) acc
  | .whileStmt _ t b =>
      let acc := walkStmt (walkExpr acc t) b
      { acc with hasUnloweredLoopShape := true }
  | .doWhileStmt _ b t =>
      let acc := walkExpr (walkStmt acc b) t
      { acc with hasUnloweredLoopShape := true }
  | s@(.forStmt _ init t u b) =>
      -- Walk order: init, test, body, THEN the update — `accAfterBody`
      -- excludes the structural `i++` so it can't poison the loop var.
      let accBeforeBody := match init with
        | some (.inl e) => walkExpr acc e
        | some (.inr vd) => walkStmt acc (.variableDecl vd)
        | none => acc
      let accBeforeBody := match t with | some e => walkExpr accBeforeBody e | none => accBeforeBody
      let accAfterBody := walkStmt accBeforeBody b
      let accFinal := match u with | some e => walkExpr accAfterBody e | none => accAfterBody
      match LoopShape.classifyLoop s with
      | .canonicalFor v bound _ =>
          -- Containment, not a before/after diff: a shadowing loop var shares
          -- its string key with outer vars, so the diff is unreliable. This
          -- false-poisons a clean loop under a same-named mutated outer var,
          -- but is always sound (tested).
          let vMutatedAfterBody := accAfterBody.mutated.contains v
          let boundMutated := match bound with
            | .inr arrName => accAfterBody.mutated.contains arrName
            | .inl _ => false
          if vMutatedAfterBody || boundMutated
              || LoopShape.hasLabeledBreakOrContinue b then
            { accFinal with hasUnloweredLoopShape := true }
          else
            { accFinal with hasLowerableLoop := true }
      | _ => { accFinal with hasUnloweredLoopShape := true }
  | s@(.forOfStmt _ left r b _) =>
      -- Walk children first so the mutated set is populated, then classify.
      let acc := match left with
        | .inl e => walkExpr acc e
        | .inr vd => walkStmt acc (.variableDecl vd)
      let acc := walkStmt (walkExpr acc r) b
      match LoopShape.classifyLoop s with
      | .forOf v _ _ _ =>
          -- No update clause to exclude, so the full accumulator is checked;
          -- same containment conservatism as canonicalFor.
          if acc.mutated.contains v || LoopShape.hasLabeledBreakOrContinue b then
            { acc with hasUnloweredLoopShape := true }
          else
            { acc with hasLowerableLoop := true }
      | _ => { acc with hasUnloweredLoopShape := true }
  | .forInStmt _ left r b =>
      let acc := match left with
        | .inl e => walkExpr acc e
        | .inr vd => walkStmt acc (.variableDecl vd)
      let acc := walkStmt (walkExpr acc r) b
      { acc with hasUnloweredLoopShape := true }
  | .switchStmt _ d cases =>
      -- Lowerable switch shape: a discriminated-union dispatch
      -- (`switch (ident.field)`, non-computed) where every arm returns and
      -- there is no `default`. Anything else — including a plain-identifier
      -- scrutinee, which the emitter has no lowering for — keeps the
      -- function out of do-mode.
      let discriminatedShape := match d with
        | .memberExpr _ (.identifier _ _) (.identifier _ _) false _ => true
        | _ => false
      let unlowered := !discriminatedShape
        || cases.any fun (.mk _ t ss) => t.isNone || !stmtsReturn ss
      let acc := if unlowered then { acc with hasUnloweredSwitchShape := true } else acc
      cases.foldl (fun a (.mk _ t ss) =>
        let a := match t with | some e => walkExpr a e | none => a
        ss.foldl walkStmt a) (walkExpr acc d)
  | .tryStmt _ b h f =>
      let acc := walkStmt { acc with hasTryShape := true } b
      let acc := match h with | some (.mk _ _ hb _) => walkStmt acc hb | none => acc
      match f with | some s => walkStmt acc s | none => acc
  | .withStmt _ _ b => walkStmt acc b
  | .labeledStmt _ _ b =>
      -- Labels on loops poison do-mode wholesale (`emitBodyDo` has no
      -- labeledStmt lowering); labeled break/continue inside bodies is
      -- poisoned separately via hasLabeledBreakOrContinue.
      let acc := walkStmt acc b
      if LoopShape.isLoopStmt b then { acc with hasUnloweredLoopShape := true }
      else acc
  | .functionDecl _ _ _ body _ _ =>
      -- nested function declaration: everything it references is a capture
      { acc with capturedRefs := insertAll acc.capturedRefs (identsStmt body) }
  | _ => acc
end

/-- Analyze one function: parameter names + body statement. -/
def analyze (paramNames : List String) (body : Statement) : MutationInfo :=
  let acc : MutationInfo := { params := insertAll {} paramNames }
  walkStmt acc body

end Thales.Emit.EscapeAnalysis
