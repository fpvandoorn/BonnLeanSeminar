import Mathlib.Tactic
-- set_option linter.unusedVariables false
-- set_option linter.unusedTactic false
open Lean Meta Elab

/- Tag-attributes give an easy way to tag a collection of declarations,
or to run a command on the tagged declarations. -/

initialize myAttribute : TagAttribute ←
  registerTagAttribute `my_attribute "My new attribute."
    fun nm ↦ logInfo m!"Added attribute to declaration {nm}!"

-- @[my_attribute] def f : Nat := 10









/- Parametric attributes can have parameters. -/

/-- My cool dualize attribute! -/
syntax (name := dualize) "dualize" ident : attr



initialize registerTraceClass `dualize

def translation : NameMap Name := .ofList [(`LT.lt, `GT.gt), (`LE.le, `GE.ge)]

def traverseExpr (e : Expr) : Expr :=
  e.replaceRec fun _r e ↦
    match e with
    | .const oldName ls => Id.run do
      if let some newName := translation.find? oldName then
        return some (mkConst newName ls)
      else
        return none
    | _ => none

def elabDualize : Syntax → CoreM Name
  | `(attr|dualize $nm) => pure nm.getId
  | _ => throwUnsupportedSyntax

/- Options to build a expressions:
* Modify an existing expression using e.g. Expr.replace
* Build from the absolute basic building blocks: Expr.app, Expr.lam, ...
* Build using forallTelescope, MkAppM, mkLambdaFVars, ...
* Use the Qq library to build expressions using a syntax similar to the one used in Lean code.
-/
-- open Qq

def getNewValue (nm : Name) : AttrM Expr := do
  let some (.thmInfo decl) := (← getEnv).find? nm | unreachable!
  MetaM.run' do
    forallTelescope decl.type fun args _conclusion => do
      trace[dualize] "Declaration has arguments {args} and conclusion {_conclusion}"
      if args.size < 2 then
        throwError "theorem must have at least two arguments."
      trace[dualize] "First argument {args[0]!} has type {← inferType args[0]!} which is a \
        {(← inferType args[0]!).ctorName}"
      let dualizeType ← mkAppM `OrderDual #[args[0]!]
      trace[dualize] "Dualized type: {dualizeType} which has type {← inferType dualizeType}"
      let lemmaApp ←  mkAppOptM nm #[dualizeType, none]
      trace[dualize] "Previous lemma applied: {lemmaApp} which has type {← inferType lemmaApp}"
      let newValue ← mkLambdaFVars #[args[0]!, args[1]!] lemmaApp
      trace[dualize] "New expression: {newValue} which has type {← inferType newValue}"
      return newValue

      -- trace[dualize] "Current local context {(← getLCtx).size} and instances {(← getLocalInstances).size}"

      -- let .sort firstArgLevel ← inferType args[0]! |
      --   throwError "first argument must be a sort."
      -- let α : Q(Type) := args[0]!
      -- let tp : Q(Type) := q(OrderDual $α)
      -- let dualizeType := mkConst `OrderDual [firstArgLevel] |>.app args[0]!

      -- let lemmaApp ←  mkAppOptM nm #[dualizeType, none]
      -- let instApp ←  mkAppOptM `OrderDual.instPreorder #[args[0]!, args[1]!]
      -- trace[dualize] "Instance: {instApp} which has type {← inferType instApp}"
      -- let lemmaApp ←  mkAppOptM nm #[dualizeType, instApp]


def evalDualize (nm : Name) (stx : Syntax) : AttrM Name := do
  let tgt ← elabDualize stx
  trace[dualize] "Dualizing {nm} to {tgt}"
  let some (.thmInfo decl) := (← getEnv).find? nm |
    throwError "declaration '{nm}' is not a theorem."
  let newType := traverseExpr decl.type
  trace[dualize] "New type: {newType}"
  let newValue ← getNewValue nm
  addDecl <| .thmDecl {
    name := tgt
    levelParams := decl.levelParams
    type := newType
    value := newValue
  }
  pushInfoLeaf <| .ofTermInfo {
    elaborator := .anonymous, lctx := {}, expectedType? := none, isBinder := true,
    stx := stx, expr := ← mkConstWithLevelParams tgt }
  return tgt

initialize dualizeAttr : ParametricAttribute Name ←
  registerParametricAttribute {
    name := `dualize
    descr := "Dualize a lemma.",
    getParam := evalDualize }
