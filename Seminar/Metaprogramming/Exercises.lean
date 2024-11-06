import Mathlib

set_option linter.unusedVariables false
set_option linter.unusedTactic false
open Lean Meta Elab Parser Tactic PrettyPrinter Command Delaborator

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
(a) Define a tactic that repeatedly tries to apply introduction rules for implications, forall, negation and conjunction, and calls `assumption` to close the goals. Test it on a few statements.

(b) Extend the tactic to also apply the introduction rule for the existential quantifier and test it on a few statements.

(c) Extend the tactic to also apply the introduction rule for the disjunctions, trying one constructor first, and if it fails to close the goal, try the other constructor. Test it on a few statements.

(d) Make sure that if the tactic fails, the resulting goal is what you get by only applying the safe rules (from part (a)), and the rules from parts (b) and (c) are not applied if they didn't close the goal. Test that you get the correct goal state on a few examples.

Remark: To apply elimination rules, we would need more metaprogramming
(e.g. to loop through all local hypotheses).
Hint: I didn't actually try to write this myself, but I'm reasonably confident
that this is all doable just by using macro/macro_rules.
Hint 2: you might need to use `guard_target = _ ∧ _` or similar to check what the current goal is.
-/
