import
  .pSet_ordinal
  .bvm_extras
  .bvm
  .to_mathlib
  set_theory.zfc
  set_theory.cardinal
  set_theory.ordinal
  order.complete_boolean_algebra

universes u v

namespace pSet

section 
open cardinal

noncomputable def aleph_one : pSet := card_ex (aleph 1)

--   (Ord x) ⊓ (⨅ y, (Ord y) ⟹ ((- injects_into y bSet.omega) ⟹ x ⊆ᴮ y))
def aleph_one_Ord_spec (x : pSet.{u}) : Prop := 
Ord x ∧ (∀ y : pSet.{u}, Ord y ∧ ¬ injects_into y pSet.omega → x ⊆ y)

lemma aleph_one_satisfies_spec : aleph_one_Ord_spec aleph_one := sorry

lemma Ord.trichotomy {x y : pSet.{u}} (Hx : Ord x) (Hy : Ord y) : equiv x y ∨ x ∈ y ∨ y ∈ x := sorry

lemma Ord.lt_of_le_of_lt {x y z : pSet.{u}} (Hx : Ord x) (Hy : Ord y) (Hz : Ord z) (H_le : x ⊆ y) (H_lt : y ∈ z) : x ∈ z :=
begin
  have := Ord.trichotomy Hx Hy,
  have H_dichotomy : x ∈ y ∨ equiv x y,
    by {cases this, right, from ‹_›, cases this, left, from ‹_›,
        right, rw equiv.ext, refine ⟨‹_›,_⟩, apply Hx.right, from ‹_› },
  cases H_dichotomy,
    { apply mem_trans_of_transitive, from ‹_›, from ‹_›, from Hz.right },
    { rwa mem.congr_left (equiv.symm H_dichotomy) at H_lt }
end

lemma Ord_of_mem_Ord {x z : pSet.{u}} (H_mem : x ∈ z) (H : Ord z) : Ord x := sorry

lemma injects_into_omega_of_mem_aleph_one (x : pSet.{u}) (H_mem : x ∈ (aleph_one : pSet.{u})) : injects_into x pSet.omega :=
begin
  cases aleph_one_satisfies_spec with spec₁ spec₂,
  classical, by_contra H, specialize spec₂ x ⟨(Ord_of_mem_Ord H_mem ‹_›), ‹_›⟩,
  suffices : aleph_one ∈ aleph_one,
    by exact mem_self ‹_›,
  apply Ord.lt_of_le_of_lt, from ‹_›, from (Ord_of_mem_Ord H_mem ‹_›),
  repeat {assumption}
end

end 

end pSet
open lattice bSet cardinal
namespace bSet

section

variables {𝔹 : Type u} [nontrivial_complete_boolean_algebra 𝔹]

local notation `ℵ₁` := pSet.aleph_one

local infix ` ⟹ `:65 := lattice.imp

local infix ` ⇔ `:50 := lattice.biimp

local infix `≺`:70 := (λ x y, -(larger_than x y))

local infix `≼`:70 := (λ x y, injects_into x y)

lemma injects_into_omega_of_mem_aleph_one_check {Γ : 𝔹} {z : bSet 𝔹} (H_mem : Γ ≤ z ∈ᴮ (ℵ₁)̌ ): Γ ≤ injects_into z bSet.omega :=
begin
  rw mem_unfold at H_mem, bv_cases_at H_mem η Hη, simp at Hη,
  suffices : Γ_1 ≤ injects_into (ℵ₁̌.func η) bSet.omega,
  apply bv_rw' Hη, simp, from ‹_›,
  suffices : pSet.injects_into ((ℵ₁).func $ check_cast η) pSet.omega,
    by {rw check_func, apply check_injects_into, from ‹_› },
  apply pSet.injects_into_omega_of_mem_aleph_one,
  by simp
end

lemma mem_aleph_one_of_injects_into_omega {x : bSet 𝔹} {Γ : 𝔹} (H_aleph_one : Γ ≤ aleph_one_Ord_spec x) {z : bSet 𝔹} (H_z_Ord : Γ ≤ Ord z) (H_inj : Γ ≤ injects_into z bSet.omega) : Γ ≤ z ∈ᴮ x :=
begin
  sorry
-- suppose that z ∉ x. then by trichotomy, z = x or x ∈ z.
-- if z = x, then x injects into z, which is bad, so we need to additionally add a clause which says that aleph_one itself does not inject into omega.
-- if x ∈ z, then x ⊆ z, which again means that x injects into omega (via injects_into trans and le_of_subset)
end

lemma aleph_one_check_sub_aleph_one_axiom_aux {x : bSet 𝔹} {Γ : 𝔹} (H_aleph_one : Γ ≤ aleph_one_Ord_spec x) : Γ ≤ ℵ₁̌ ⊆ᴮ x :=
begin
  rw subset_unfold', bv_intro w, bv_imp_intro H_mem_w,
  apply mem_aleph_one_of_injects_into_omega, from ‹_›,
  exact Ord_of_mem_Ord H_mem_w
    (check_Ord (by {unfold pSet.aleph_one pSet.card_ex, simp })),
  exact injects_into_omega_of_mem_aleph_one_check ‹_›
end

end 


end bSet




/- For this release, we axiomatize the existence of ℵ₁ and its specification. -/

-- there exists a least ordinal not injecting into ω
axiom aleph_one_exists_axiom {𝔹 : Type*} [nontrivial_complete_boolean_algebra 𝔹] {Γ : 𝔹} : Γ ≤ ⨆x, aleph_one_Ord_spec x

-- -- ℵ₁̌  ⊆ ℵ₁. This is generally true for all nontrivial 𝔹 and cardinals κ.
-- axiom aleph_one_check_sub_aleph_one_axiom  {𝔹 : Type*} [nontrivial_complete_boolean_algebra 𝔹] {Γ : 𝔹}
--   : Γ ≤ (pSet.card_ex (aleph 1))̌  ⊆ᴮ classical.some (maximum_principle aleph_one_Ord_spec (by simp))

-- ℵ₁ is the successor cardinal of ω
axiom aleph_one_le_of_omega_lt_axiom {𝔹 : Type*} [nontrivial_complete_boolean_algebra 𝔹] {Γ : 𝔹}
  : Γ ≤ le_of_omega_lt (classical.some (maximum_principle aleph_one_Ord_spec (by simp)))


