/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Data.Finset.Card
import Mathlib.Topology.Instances.ENNReal

/-!
# Lemmas to be Ported to Mathlib

This file gives a centralized location to add lemmas that belong better
in general mathlib than in the project itself.
-/

open BigOperators ENNReal

lemma Fintype.sum_inv_card (α : Type) [Fintype α] [Nonempty α] :
  Finset.sum Finset.univ (λ _ ↦ (Fintype.card α)⁻¹ : α → ℝ≥0∞) = 1 := by
  rw [Finset.sum_eq_card_nsmul (λ _ _ ↦ rfl), Finset.card_univ,
    nsmul_eq_mul, ENNReal.mul_inv_cancel] <;> simp

/-- Summing `1` over list indices that satisfy a predicate is just `countP` applied to `p`. -/
lemma List.countP_eq_sum_fin_ite {α : Type} (xs : List α) (p : α → Bool) :
    (∑ i : Fin (xs.length), if p xs[i] then 1 else 0) = xs.countP p := by
  induction xs with
  | nil => simp only [List.countP_nil, List.length_nil, Finset.univ_eq_empty, getElem_fin,
      List.getElem_eq_get, Fin.eta, Finset.sum_boole, Finset.filter_congr_decidable,
      Finset.not_mem_empty, IsEmpty.forall_iff, Finset.filter_true_of_mem, Finset.card_empty,
      CharP.cast_eq_zero]
  | cons x xs h => {
    rw [List.countP_cons]
    cases hp : p x
    · simp [h]
      sorry
    · sorry }

@[simp]
lemma Vector.getElem_eq_get {α n} (xs : Vector α n) (i : ℕ) (h : i < n) :
  xs[i]'h = xs.get ⟨i, h⟩ := rfl
