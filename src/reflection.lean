/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
import .fol .abel tactic.ring .completeness .zfc

open fol

local notation h :: t  := dvector.cons h t
local notation `[]` := dvector.nil
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

namespace reflection
section

/- rephrasing of soundness -/
def by_reflection {L} (T : Theory L) {S : Structure L} [h_nonempty : nonempty S]
  {hS : S ⊨ T} (p : Prop) (ψ : sentence L) (h_p : realize_sentence S ψ ↔ p) : T ⊢' ψ → p :=
by {intro P, cases P, apply h_p.mp, apply soundness, repeat{assumption}}

open abel

/- every abelian group satisfies ∀ x ∀ y, x + (y + y) = y + (y + x) -/
def T_ab_proves_x_y_y : T_ab ⊢' ∀' ∀' (&1 +' (&0 +' &0) ≃ &0 +' (&0 +' &1)) :=
begin
  apply (completeness _ _).mpr, intros M h_nonempty hM,
  intros x y, unfold T_ab at hM,
  have  hM' : M ⊨ a_comm ∧ M ⊨ a_inv ∧ M ⊨ a_zero_left ∧ M ⊨ a_zero_right ∧ M ⊨ a_assoc,
  by {simp at hM, assumption}, rcases hM' with ⟨uno,dos,tres,cuatro,cinco⟩,
  have this1 := cinco x y y, have this2 := uno y x, have this3 := uno (realize_bounded_term ([x,y]) (&0 +' &1) []) y, dsimp at *,
  conv {to_lhs, change realize_bounded_term ([y, y, x]) (&2 +' (&1 +' &0)) [], rw[<-this1]},
  conv {to_lhs, change realize_bounded_term ([y, (realize_bounded_term ([x, y]) (&0 +' &1) [])]) (&1 +' &0) [], rw[this3, <-(this2)]}, refl
end

example : ∀ x y : ℤ, x + (y + y) = y + (y + x) :=
begin
  apply @by_reflection L_abel T_ab ℤ' (by apply_instance) (ℤ'_is_abelian_group) _ _ _ _,
  exact ∀' ∀' (&1 +' (&0 +' &0) ≃ &0 +' (&0 +' &1)), {refl}, exact T_ab_proves_x_y_y
end

example : ∀ x y : ℤ, x + (y + y) = y + (y + x) :=
by {intros, rw[add_comm,add_assoc]}

example : ∀ x y : ℤ, x + (y + y) = y + (y + x) :=
by {intros, ring}

example : ∀ x y : ℤ, x + (y + y) = y + (y + x) :=
by {simp}

example : ∀ x y : ℤ, x + (y + y) = y + (y + x) :=
by {tidy}

def L_abel_structure_of_add_group (α : Type) [add_group α] : Structure L_abel :=
begin
  refine ⟨α, λn f, _, λn r, by {cases r}⟩,
  {induction f, intro xs, exact 0,
    intro xs,
    exact (xs.nth 0 dec_trivial) + (xs.nth 1 dec_trivial)}
end

variables (α : Type) [add_group α]

local notation `α'` := L_abel_structure_of_add_group α

@[simp]lemma α'_α : ↥(α') = α := by refl

@[reducible]instance has_zero_α' : has_zero α' := ⟨(0 : α)⟩

@[reducible]instance has_add_α' : has_add α' := ⟨λx y, (x + y : α)⟩

@[reducible]instance nonempty_α' : nonempty α' := ⟨0⟩

@[simp]lemma zero_is_zero : @realize_bounded_term L_abel α' _ [] _ zero [] = (0 : α) := by refl

@[simp]lemma plus_is_plus_l : ∀ x y : α', realize_bounded_term ([x,y]) (&0 +' &1) [] = x + y := by {intros, refl}

@[simp]lemma plus_is_plus_r : ∀ x y : α', realize_bounded_term ([x,y]) (&1 +' &0) [] = y + x := by {intros, refl}

theorem add_group_is_abelian_group {α : Type} [add_group α] : T_ab ⊆ Th(L_abel_structure_of_add_group α) :=
begin
  intros a H, repeat{cases H},
  {intros x y, change x + y = y + x, simp[add_comm], sorry},
  repeat{sorry}
  -- {intros x H, dsimp at H, unfold realize_bounded_formula, have : ∃ y : ℤ, x + y = 0,
  -- by {refine ⟨-x, _⟩, simp}, rcases this with ⟨y, hy⟩, apply H y, simp[hy], refl},
  -- {intro x, change 0 + x = x, rw[zero_add]},
  -- {intro x, change x + 0 = x, rw[add_zero]},
  -- {intros x y z, change x + y + z = x + (y + z), rw[add_assoc]}
end


example : ∀ x y : α, x + (y + y) = y + (y + x) :=
begin sorry
  -- apply @by_reflection L_abel T_ab ℤ' (by apply_instance) (ℤ'_is_abelian_group) _ _ _ _,
  -- exact ∀' ∀' (&1 +' (&0 +' &0) ≃ &0 +' (&0 +' &1)), {refl}, exact T_ab_proves_x_y_y
end

end
end reflection
