import Seminar.Metaprogramming.Attribute
open Lean Meta Elab


@[my_attribute] def f : Nat := 10
@[my_attribute] def c : Nat := 3
@[my_attribute] lemma some_lemma : 1 + 1 = 2 := rfl


run_cmd do
  let state := myAttribute.ext.getState (← getEnv)
  logInfo m!"State: {state.toList}"


attribute [my_attribute] f












set_option trace.dualize true

whatsnew in
@[dualize my_ge_trans]
lemma my_le_trans {α : Type*} [Preorder α] {a b c : α} :
    a ≤ b → b ≤ c → a ≤ c := le_trans

-- lemma my_ge_trans : ∀ {α : Type*} [Preorder α] {a b c : α},
--     a ≥ b → b ≥ c → a ≥ c := @fun α _ ↦ @my_le_trans αᵒᵈ _

#print my_ge_trans



-- whatsnew in
@[dualize gt_ge_trans]
lemma lt_le_trans {α : Type*} [Preorder α] {a b c : α} :
    a < b → b ≤ c → a < c := lt_of_lt_of_le
