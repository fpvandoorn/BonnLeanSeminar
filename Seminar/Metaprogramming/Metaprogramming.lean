import Mathlib.Tactic
set_option linter.unusedVariables false
set_option linter.unusedTactic false
open Lean Meta Elab Parser Tactic Command PrettyPrinter Delaborator

/- # Metaprogramming intro -/

/-
Since Monday there is a WIP Lean reference available here:
https://lean-lang.org/doc/reference/latest/
It's still WIP and missing many chapters, but it already contains a lot of information.
-/

/- We will learn the basics of:
* notation
* macros
* tactics
-/


/-! ## Getting Started -/

/- Notation in Lean is extensible. You can define your own notation. Here is a simple example. -/

notation "𝔽₂" => ZMod 2

example (n : 𝔽₂) : n + n = 0 := by rw [CharTwo.add_self_eq_zero]





/- Here we define our own infix notation, the `:65` specifies the *precedence* of the notation.
Multiplication has higher precedence than addition. -/

#check 1 + 1
infix:65 (priority := low) " +' " => HAdd.hAdd
#eval 3 +' 5 * 2

/- Simple notation is also used by the pretty printer -/
#check 3 + 5


/- You can also define more complicated notations, like notation that binds a variable. -/

notation3 "do_twice" (...) " ↦ "
  c:60:(scoped f => f ∘ f) => c

#check do_twice x : ℕ ↦ x ^ 2
#check (do_twice x ↦ x ^ 2) 3
#eval (do_twice x ↦ x ^ 2) 3


/- If you want to declare your own notation,
I recommend copying and modifying an existing notation declaration from Mathlib. -/


/- You can be even more flexible with *macros*. -/
macro "∑ " x:ident " ∈ " l:term ", " f:term : term => `(List.sum (List.map (fun $x => $f) $l))

variable (x : ℕ)
#check ∑ y ∈ [1,2,3], (y ^ 3 + x)

/- Remark: macros are not automatically pretty-printed. -/
#check ∑ x ∈ [1,2,3], x ^ 3



/- Declaring your own pretty-printer is a bit cumbersome. -/

@[app_unexpander List.sum]
def unexpListMap : Unexpander
  | `($_ $a) =>
    match a with
    | `(List.map $f $l) =>
      match f with
      | `(fun $x:ident ↦ $f) => `(∑ $x ∈ $l, $f)
      | _ => throw ()
    | _ => throw ()
  | _ => throw ()

#check ∑ x ∈ [1,2,3], x ^ 3
#check ∑ i ∈ Finset.empty, i

/- You can also declare macros for tactics, commands or similar.
`(...) stands for "quotation". It reflects terms/tactics/commands into Syntax objects. -/

macro "split" : tactic => `(tactic| constructor)
macro "quit" : tactic => `(tactic| all_goals sorry)

example : 2 + 2 = 5 ∧ 5 < 6 := by
  split
  quit


/- Note the difference between `t` and `s` in the following example -/
run_cmd do
  let t ← `(term|(3 + 1) * (3 +' 1))
  logInfo m!"{t}"
  let t2 ← `(($t) + ($t))
  logInfo m!"{t2}"
  let s := (3 + 1) * (3 +' 1)
  logInfo m!"{s}"
  let s2 ← `((s) + (s)) -- wrong s
  logInfo m!"{s2}"
  let z ← `(tactic| all_goals sorry)
  logInfo m!"{z}"
  return

/- There are different syntax categories -/

#check `(1+1)
#check `(term|(3 + 1) * (3 +' 1))
#check `(tactic| constructor)
#check `(command| #eval 1+1)



/- We can also write commands using macros. -/

macro "#show" t:term : command => `(command|#check $t)

#show 5
#synth AddGroup ℤ

/- In fact, the commands `infix` and `notation` are themselves implemented using macros,
They are macros that generate new macros. -/





/-
`macro` is short for `syntax` + `macro_rules`.
You can declare multiple macro rules
-/

syntax (name := myName) "easy" : tactic

-- example : True := by easy

macro_rules | `(tactic|easy) => `(tactic|assumption)
macro_rules | `(tactic|easy) => `(tactic|focus (simp; first | done | easy))
macro_rules | `(tactic|easy) => `(tactic|focus (ring_nf; done))
-- macro_rules | `(tactic|easy) => `(tactic|skip; easy)

example : False := by simp

example (n m : ℕ) (h : n ≠ m) : n ≠ m ∧ n + m = m + n ∧ 0 ≤ n := by
  refine ⟨?_, ?_, ?_⟩
  all_goals easy



/- With macros we can write down some shortcuts combining existing tactics.
For more control, it is useful to use `elab`.

Let's see some examples. -/

elab "my_tac" : tactic => logInfo "Hello"

example : True := by
  my_tac
  trivial

/- We can use `do` to execute multiple instructions. -/

elab "my_tac2" : tactic => do
  logInfo "Hello"
  logInfo "world."

example : True := by
  my_tac2
  trivial

/- We can throw errors using `throwError`. -/

elab "my_failure" : tactic => do
  logInfo "Hello"
  throwError "Oops"

example : True := by
  my_failure


/- `t <|> t'` executes `t`, and only if `t` fails, we execute `t'` instead. -/

elab "try_hard" : tactic => do
  throwError "Oops" <|> logInfo "Ok"

example : True := by
  try_hard
  trivial



/- To do something nontrivial, we have to get information from the context.
We do this using `let x ← t`. This executes `t` and stores the result in `x`. -/

elab "report" : tactic => do
  let tgt ← getMainTarget
  logInfo m!"Current goal: {tgt}"

example : 1 + 1 = 2 := by
  report
  trivial

example : ∀ p q : ℕ, p + q = q + p  := by
  report
  exact add_comm

/- We can abbreviate this by using `← t` anywhere to mean "the result of running `t`" -/

elab "report2" : tactic => do
  logInfo m!"Current goal: {← getMainTarget}"

example : ∀ p q : ℕ, p + q = q + p := by
  report2
  exact add_comm





/-! ## Some Monads -/

/- Parsing doesn't seem to use monads. -/

/- The most important monads
* IO: can read/write files, do network requests, etc.
* CoreM: IO + can read and modify the environment
* MetaM: CoreM + can work with metavariables
* TermElabM: MetaM + can elaborate terms (e.g. contains a list of metavariables that should still be resolved)
* TacticM: TermElabM + a list of open goals (for tactics)
-/
#check IO
#check CoreM
#check MetaM
#check TermElabM
#check TacticM
-- #check MetaM.run
/-
For reference, the Mathlib wiki has a monad map
https://github.com/leanprover-community/mathlib4/wiki/Monad-map

Below are some other monads, but let's ignore them for now.
-/

/- Macros -/
#check MacroM -- Exception + context + state

/- Commands -/
#check CommandElabM -- IO + context + state

/- Pretty-printing -/
#check DelabM -- MetaM + context + state
#check UnexpandM -- Exception + can read syntax
#check FormatterM -- CoreM + context + state

/- Some important concepts -/

/- A name is basically a list of strings.
All elements except the last are the namespaces corresponding to that name.
(Names can also contain numerical components,
which is used for some internal purposes) -/
#check Name
#check `Nat.add
#eval `Nat.add
#eval `Nat ++ `add
#eval (Name.anonymous.str "Nat").str "add"

/- An expression is an (elaborated) term.
It can be a
* bound variable (the second `x` in `fun x ↦ x`)
* free variable (hypotheses in the local context)
* metavariable (terms to be synthesized)
* sort (`Type _`)
* constant (any declaration)
* application
* lambda (fun x : ℕ ↦ f x)
* forall (including Pi-types / arrow types)
* A let expression (`let x := 3; x + x`)
* A literal (an explicit string or number)
* an expression tagged with some metadata
  (e.g. an annotation to print an expression in a certain way)
* a projection (think of `x.1` for `x : α × β`) (*)
-/
#print Expr
#check (5 : ℤ)
#check fun x : ℕ × ℕ ↦ x.1
#print Prod.fst


/-! ## Let's write some basic tactics -/

/- Now let's implement an actual tactic: the assumption tactic.
We go through each assumption and look whether the type of the assumption is
*definitionally equal* to the target. -/

elab "my_assumption" : tactic => withMainContext do
  /- A *goal* in a tactic state consists of a metavariable that
  will be instantiated with the proof term after executing the tactic script.
  `getMainTarget` gives the type of the metavariable (i.e. the goal). -/
  let target ← getMainTarget
  /- Loop through all hypotheses in the local context -/
  for ldecl in ← getLCtx do
    /- Ignore certain "implementation details"
    (these are also not printed in the goal) -/
    if ldecl.isImplementationDetail then continue
    -- logInfo m!"Checking hypothesis {ldecl.type}"
    /- Check for *definitional equality* -/
    if ← withReducible (isDefEq ldecl.type target) then
      /- -/
    closeMainGoal `my_assumption ldecl.toExpr
    return
  throwTacticEx `my_assumption (← getMainGoal)
    m!"unable to find matching hypothesis of type {indentExpr target}"

theorem foo (n m : ℕ) (h1 : 0 ≤ m) (h2 : n = 0) (h3 : m ≤ 9) : n = 0 := by
  my_assumption


example (p q : ℕ) : p + q = q + p := by
  my_assumption


/- The example below works at `semireducible` transparency,
but not at reducible transparency. -/

@[reducible] def double (x : ℕ) : ℕ := x + x

example (n : ℕ) (h1 : double n = 12) : n + n = 12 := by
  my_assumption








/- As a second example, we want to write a tactic that creates a new hypothesis
`a₁ + a₂ = b₁ + b₂` from the assumptions `a₁ = b₁` and `a₂ = b₂`. -/

example (a b c d : ℕ) (h : a = b) (h' : c = d) : a + c = b + d := by
  have H := congrArg₂ HAdd.hAdd h h'
  exact H

elab "add_eq" eq₁:ident eq₂:ident " with " new:ident : tactic =>
  withMainContext do -- ignore this for now
    let newTerm  ← `(congrArg₂ HAdd.hAdd $eq₁ $eq₂)
    let prf ← elabTerm newTerm none
    let typ ← inferType prf
    let (_newFVars, newGoal) ← (← getMainGoal).assertHypotheses
      #[{userName := new.getId, type := typ, value := prf}]
    replaceMainGoal [newGoal]

example (a b c d : ℕ) (h : a = b) (h' : c = d) : a + c = b + d := by
  add_eq h h' with H
  exact H

/- If we want to be more flexible, and make the `with H` optional,
we can do this by separately declare a syntax and elaboration rules for that syntax.
elab = syntax + elab_rules -/

syntax "add_eq'" ident ident ("with" ident)? : tactic

elab_rules : tactic
| `(tactic| add_eq' $eq₁:ident $eq₂:ident $[with $new]?) => do
  logInfo m!"{new}" -- we print the variable `new`
  withMainContext do
    let newTerm  ← `(congr (congrArg HAdd.hAdd $eq₁) $eq₂)
    let prf ← elabTerm newTerm none
    let typ ← inferType prf
    -- we use the name `new`, or make a name ourselves
    let newName := match new with
    | some ident => ident.getId
    | none => `newEq
    let (_newFVars, newGoal) ← (← getMainGoal).assertHypotheses
      #[{userName := newName, type := typ, value := prf}]
    replaceMainGoal [newGoal]

example (a b c d : ℕ) (h : a = b) (h' : c = d) : a + c = b + d  := by
  add_eq' h h'
  my_assumption


/- Let's see what goes wrong when we don't write `withMainContext`. -/
example (a b c d : ℕ) (h : a = b) : c = d → a + c = b + d  := by
  intro h'
  add_eq' h h' with H
  assumption





/- Here we do something similar:
we multiply both sides of a hypothesis by
a constant -/

example (a b c : ℤ) (hyp : a = b) : c*a = c*b := by
  replace hyp := congr_arg (fun x ↦ c*x) hyp
  exact hyp

elab "mul_left" x:term l:location : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    match expandLocation l with
    | .targets #[hyp] false => do
      let hypTerm : Term := ⟨hyp⟩
      let prfStx ← `(congr_arg (fun y ↦ $x*y) $hypTerm)
      let prf ← elabTerm prfStx none
      let typ ← inferType prf
      let fvarId ← getFVarId hyp
      let (_newFVars, newGoal) ← goal.assertHypotheses
        #[{userName := hyp.getId, type := typ, value := prf}]
      replaceMainGoal [← newGoal.clear fvarId]
    | _ => throwError "You can use this tactic only at one hypothesis."


example (a b c : ℤ) (hyp : a = b) : c*a = c*b := by
  mul_left c at hyp
  exact hyp


/- Let's take another look at the environment -/

#check Environment

run_cmd do
  let env ← getEnv
  let nConsts := env.constants.fold (init := 0) fun n _ _ ↦ n + 1
  logInfo m!"Number of constants known to Lean: {nConsts}"
  let nConsts' := env.const2ModIdx.size
  logInfo m!"Number of constants in imported files, including some hidden constants \
    (e.g. constants generated by the code generator that will never be sent to the Lean kernel): \
    {nConsts'}" -- notice the escapes for line breaks.
  logInfo m!"Current Module: {env.mainModule}"
  logInfo m!"Direct imports: {env.imports}"
  logInfo m!"Number of (indirect) imports: {env.header.moduleNames.size}"

/- Note: `run_cmd` runs a program in the `CommandElabM` monad,
If you need something from `CoreM` or `MetaM`, use `run_meta`. -/
#print InductiveVal
#print ConstantVal
#print ConstantInfo
run_meta do
  let nm1 := `Nat.add -- use any def here
  let c1 := (← getEnv).find? nm1 |>.get!
  logInfo m!"{nm1} has type {c1.type} and value\n {c1.value!}"
  let .defnInfo d1 := c1 | unreachable!
  logInfo m!"We can also obtain its value this way:\n {d1.value}"

  let nm2 := `Group -- use another structure/class/inductive here
  let c2 := (← getEnv).find? nm2 |>.get!
  logInfo m!"{nm2} has type {c2.type}"
  let .inductInfo d2 := c2 | unreachable!
  logInfo m!"{nm2} has {d2.numParams} parameter(s), {d2.numIndices} indices and constructor \
    {d2.ctors.head!}"

  let nm3 := `Group -- use any structure/class here
  let c3 := getStructureInfo? (← getEnv) nm3 |>.get!
  logInfo m!"{nm3} has fields {c3.fieldNames}"



/- Some neat tricks: there are some custom term elaborators -/

#check eval% 2 + 3
#check type_of% (2 + 3)
#check fun α β γ δ ↦ (prod_assoc% : (α × β) × (γ × δ) ≃ α × (β × γ) × δ)


structure Foo where
  x : Fin 2
  y : Bool
deriving Fintype, Inhabited, Repr
