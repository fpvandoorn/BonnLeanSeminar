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
