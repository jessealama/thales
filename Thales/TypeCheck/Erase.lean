/-
  Thales/TypeCheck/Erase.lean
  Type erasure: TS AST → JS AST

  Strips all TypeScript-specific syntax, producing plain JavaScript AST
  that the existing compiler can handle unchanged.
-/
import Thales.AST
import Thales.TypeCheck.TSAST

namespace Thales.TypeCheck

open Thales.AST

/-- Erase a single TS statement to zero or more JS statements.
    Returns a list because some TS constructs (interface, type alias) erase to nothing. -/
def eraseStatement : TSStatement → List Statement
  | .js s => [s]
  | .annotatedVarDecl base kind name _typeAnn init =>
    let pattern := Pattern.identifier { name := name }
    let declarator := VariableDeclarator.mk base pattern init
    [Statement.variableDecl (VariableDeclaration.mk base [declarator] kind)]
  | .annotatedFuncDecl base name _typeParams params _returnType body generator async _throwsAnn _total =>
    let jsParams := params.map fun (paramName, _typeAnn, _optional, isRest) =>
      if isRest then FunctionParam.rest { name := paramName }
      else FunctionParam.simple { name := paramName }
    [Statement.functionDecl base { name := name } jsParams body generator async]
  | .interfaceDecl .. => []
  | .typeAliasDecl .. => []
  | .enumDecl base name members _isConst =>
    -- Erase to: var Name = { Member0: 0, Member1: 1, ... }
    -- Track running index; if a member has a literal number init, update counter
    let (props, _) := members.foldl (fun (acc : List ObjectProperty × Int) member =>
      let (propList, idx) := acc
      let valueExpr := match member.init with
        | some e => e
        | none => Expression.literal {} (.number (Float.ofInt idx)) (toString idx)
      let keyExpr := Expression.literal {} (.string member.name) s!"\"{member.name}\""
      let prop := ObjectProperty.regular {} keyExpr valueExpr "init" false false
      let nextIdx := match member.init with
        | some (Expression.literal _ (.number n) _) =>
          (Int.ofNat n.toUInt64.toNat) + 1
        | _ => idx + 1
      (propList ++ [prop], nextIdx)
    ) ([], 0)
    let objExpr := Expression.objectExpr {} props
    let pattern := Pattern.identifier { name := name }
    let declarator := VariableDeclarator.mk base pattern (some objExpr)
    [Statement.variableDecl (VariableDeclaration.mk base [declarator] .var)]
  | .declareStmt .. => []
  | .importDecl .. => []

/-- Erase a TS expression to a JS expression -/
def eraseExpression : TSExpression → Expression
  | .js e => e
  | .asExpr inner _type => eraseExpression inner
  | .satisfiesExpr inner _type => eraseExpression inner
  | .nonNullAssert inner => eraseExpression inner

/-- Erase an entire TS program to a JS program -/
def eraseProgram (prog : TSProgram) : Program :=
  let jsStmts := prog.body.flatMap eraseStatement
  { base := prog.base, body := jsStmts, sourceType := prog.sourceType }

end Thales.TypeCheck
