import Mathlib

set_option linter.unusedVariables false
set_option linter.unusedTactic false
open Lean Meta Elab Parser Tactic PrettyPrinter Command Delaborator Expr

/-!
# Exercises about meta-programming

This file contains a number of exercises on meta-programming. So far, all of them address the
seminar session on October 23 (but other exercises could follow in the future).
These exercises vary in difficulty: some may be easy, some are harder.
- exercises starred (*) are a bit harder, but should still be doable with just the seminar knowledge
- exercises starred (***) require some extra knowledge, but are definitely doable
- exercises starred (*****) are very hard: the author doesn't know a solution to these right now.
(They may have one, or not. Realising what doesn't work can also be helpful.)
-/

/-! ## Notation -/

/- Exercise 1: polynomial rings
(a) Define some notation 𝔽₃ for the field with 3 elements. -/
-- these should work now:
-- #check 𝔽₃
-- example (n : 𝔽₃) : n + n + n = 0 := by sorry

/- (b) (*) Define some notation 𝔽₃[X] for the polynomial ring over 𝔽₃ in one variable `X`. -/
--#check Polynomial

-- #check 𝔽₃[X]
-- #check 𝔽₃[Y]

/- (c) (*) Define some notation 𝔽₃[X, Y, Z] for the polynomial ring over 𝔽₃ in three variables. -/
--#check MvPolynomial
-- this should work now
-- #check 𝔽₃[X, Y, Z]

/- (d) (*****) Define notation for the polynomial ring over F₃ in `n` variables.
Part of the challenge is figuring out what good notation could be. -/
-- add a test using this yourself


/- (e) (***) Define notation 𝔽₂₃₄ for the ring ZMod 234: parse the sequence of digits
and convert them to the right number yourself. -/


/- Exercise 2: the letter ℍ -/
/- (a) define notation ℍ for the quaternions over the real numbers -/
-- #check Quaternion ℝ

/- (b) define notation ℍ for the upper half plane,
  so this notation has higher priority -/
--notation:50 "ℍ" => UpperHalfPlane
-- #check UpperHalfPlane

/- (c) What happens if you omit a precedence? What happens if you give both the same priority? -/
/- (d) (***) Find a way to determine which notation actually uses. -/
-- #check ℍ

/- (e) Write a macro `myH` which tries either notation, depending on the context. -/

def one : ℂ := ⟨0, 1⟩
def oneUH : UpperHalfPlane := UpperHalfPlane.mk one (by simp [one])

def oneQuat : Quaternion ℝ := Quaternion.coe (1 : ℝ)

-- These should work then:
-- #check myH oneUH
-- #check myH oneQuat





/-! ## Tactics -/

/- Exercise 3:
Let's try to write a very simple solver for first-order logical formulae.
(a) (*) Define a tactic that repeatedly tries to apply introduction rules for implications, forall,
negation and conjunction, and calls `assumption` to close the goals. Test it on a few statements.

(b) (*) Extend the tactic to also apply the introduction rule for the existential quantifier
and test it on a few statements.

(c) (*) Extend the tactic to also apply the introduction rule for the disjunctions,
trying one constructor first, and if it fails to close the goal, try the other constructor.
Test it on a few statements.

(d) (*) Make sure that if the tactic fails, the resulting goal is what you get by only applying the
safe rules (from part (a)), and the rules from parts (b) and (c) are not applied if they didn't
close the goal. Test that you get the correct goal state on a few examples.

Remark: To apply elimination rules, we would need more metaprogramming
(e.g. to loop through all local hypotheses).
Hint: I didn't actually try to write this myself, but I'm reasonably confident
that this is all doable just by using macro/macro_rules.
Hint 2: you might need to use `guard_target = _ ∧ _` or similar to check what the current goal is.
-/

syntax "safe_step" : tactic
syntax "safe_splitting_step" : tactic
syntax "unsafe_step" : tactic
syntax "fol" : tactic

macro_rules | `(tactic|safe_step) => `(tactic| safe_splitting_step)
macro_rules | `(tactic|safe_step) => `(tactic| intro)
macro_rules | `(tactic|safe_step) => `(tactic| assumption)

macro_rules | `(tactic|safe_splitting_step) => `(tactic| guard_target = _ ∧ _; constructor)


macro_rules | `(tactic|unsafe_step) => `(tactic| focus (guard_target = Exists _; constructor; fol; done))
macro_rules | `(tactic|unsafe_step) => `(tactic| focus (guard_target = _ ∨ _; left; fol; done))
macro_rules | `(tactic|unsafe_step) => `(tactic| focus (guard_target = _ ∨ _; right; fol; done))


macro_rules | `(tactic|fol) => `(tactic| (first | safe_step; fol | all_goals (focus unsafe_step) | skip))


example : ∀ (P : ℕ → Prop), P 3 → P 4 → ∃ n, P n ∧ P 4 := by
  fol


example : ∀ (P : ℕ → Prop), P 3 → P 4 → P 1 ∨ P 3 ∨ P 2 := by
  fol

example : ∀ (P : ℕ → Prop), P 3 → P 4 → P 3 ∧ (P 1 ∨ P 2) := by
  fol





/- ## More on tactics -/

/- Exercise 4.
(a) Define (an elaborator for) a tactic that prints all the
options you've currently set.
The list of all options has type `Lean.Options`.
Use Loogle to figure out how to get the currently set options. -/

/-
(b) Define a tactic that toggles a specific boolean option
(e.g. `profiler`, but feel free to hard-code another one) and test it.
Note: Options are in the context and not in the state,
so to implement this you have to write a tactic that takes
another tactic (sequence) as argument
You can test the profiler with the `sleep` tactic.
-/
-- example := by set_option

/-
(c) Define an *elaborator* (not a macro)
that executes a given tactic three times.
Hint: You can use `evalTactic` to evaluate tactic syntax.
-/

/- Exercise 5.
Jump to the definition of your favorite tactic, read the program it executes, and try to understand
each step. Jump into definitions of subroutines to try to understand them.
Note: often there is a declaration in the `Lean.Meta` or `Lean.MVarId` namespace
that implements most of the functionality.
Note: Don't go into the internals of term elaboration or something,
that will likely be too overwhelming.
Easy examples: `group`, `noncomm_ring`
Good/somewhat hard examples: `exact`, `constructor`, `apply`, `field_simp`, `gcongr`
Hard examples: `rw`, `ring`, `norm_num`, `abel`, `@[simps]`, `@[to_additive]`

-/

/- Exercise 6.
Let's continue with the tactic from Exercise 3.

(a) (*) Define a tactic that applies the elimination rule to all conjunctions and existential
quantifiers in the local context
(before applying introduction rules for disjunctions / existential quantifiers).

(b) (*) Define a tactic that applies the elimination rule to all disjunctions in the local context
(before applying unsafe introduction rules, after applying all safe rules)

(c) (*) For any implication `p → q` or `¬` in the local context, see if `p` occurs in the local context,
and if so, replace the implication by `q`.

(d) (*) For any universal quantifier, instantiate the quantifier with all terms in the local context
with the correct type. Make sure this doesn't loop, e.g. by just doing this step once.

(e) (***) To make sure that (d) doesn't loop, but you instantiate all the quantifiers you can,
use a monad transformer that keeps track of an additional piece of state.
This state is consists of pairs of the form (hypothesis, term) that you've already instantiated
before.
The extra state could be `Lean.RBMap` where the key is the (internal name of the) local hypothesis,
and the value is an `Array` of terms that you've already instantiated.

Optionally:
(*) Extend this tactic to handle `↔`
(*****) Extend this tactic to handle `=`

Hint: To run other tactics, writing its syntax and then using `evalTactic` is often easier than
looking at the internals of such tactics and apply those.
-/

elab "split_conjuction" : tactic => withMainContext do
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    if isAppOf ldecl.type `And then
      let nm := mkIdent ldecl.userName
      evalTactic (← `(tactic|obtain ⟨_, _⟩ := $nm))
      return
  throwTacticEx `split_conjunction (← getMainGoal)
    m!"No hypothesis is a conjunction."

macro_rules | `(tactic|safe_step) => `(tactic| split_conjuction)


example : ∀ (P Q R : Prop), P ∧ Q → Q ∧ R → P ∧ R := by
  safe_step
  safe_step
  safe_step
  safe_step
  safe_step
  safe_step
  safe_step
  safe_step
  safe_step
  safe_step

elab "split_disjunction" : tactic => withMainContext do
  let target ← getMainTarget
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    if isAppOf ldecl.type `Or then
      let nm := mkIdent ldecl.userName
      evalTactic (← `(tactic|obtain (_|_) := $nm))
      return
  throwTacticEx `split_conjunction (← getMainGoal)
    m!"No hypothesis is a disjunction."

macro_rules | `(tactic|safe_splitting_step) => `(tactic| split_disjunction)

example : ∀ (P Q R : Prop), P ∨ (Q ∨ R) → (P ∨ Q) ∨ R := by
  fol


/-

Exercise 7:
Improve an existing tactic implemented in Mathlib and PR it to Mathlib.
If you do this, post on the "Lean in Bonn" Zulip that you're working on this.

Examples:
- (***) Have the `@[gcongr]` attribute be able to recognize `↔`-lemmas
- (*****) implement one item from #1074.
  - (***) The easiest one is to let `to_additive` correctly handle `extends` clauses of structures.
- (*****) implement #11622 or #12564
- (*****) make the dualize tactic better and more robust and port it to Mathlib.
-/
