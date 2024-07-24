/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Data.Finset.Card
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Data.Vector.Defs

/-!
# Lemmas to be Ported to Mathlib

This file gives a centralized location to add lemmas that belong better
in general mathlib than in the project itself.
-/

open Mathlib BigOperators ENNReal

lemma Fintype.sum_inv_card (α : Type) [Fintype α] [Nonempty α] :
  Finset.sum Finset.univ (λ _ ↦ (Fintype.card α)⁻¹ : α → ℝ≥0∞) = 1 := by
  rw [Finset.sum_eq_card_nsmul (λ _ _ ↦ rfl), Finset.card_univ,
    nsmul_eq_mul, ENNReal.mul_inv_cancel] <;> simp

-- lemma Fin.sum_succ {α β : Type} [AddCommMonoid β]
--     (n : ℕ) (f : Fin (n + 1) → β) :
--     ∑ i : Fin (n + 1), f i = (∑ i : Fin n, f i) + f n := by
--   simp
--   rw [Fin.sum_univ_eq_sum_range]

@[simp] -- mathlib
lemma vector_eq_nil {α : Type} (xs : Vector α 0) : xs = Vector.nil :=
  Vector.ext (IsEmpty.forall_iff.2 True.intro)

lemma List.injective2_cons {α : Type} : Function.Injective2 (List.cons (α := α)) := by
  simp [Function.Injective2]

lemma Vector.injective2_cons {α : Type} {n : ℕ} :
    Function.Injective2 (Vector.cons : α → Vector α n → Vector α (n + 1)) := by
  simp [Function.Injective2, Vector.eq_cons_iff]

lemma Prod.mk.injective2 {α β : Type} :
    Function.Injective2 (Prod.mk : α → β → α × β) := by
  simp [Function.Injective2]

lemma Function.injective2_swap_iff {α β γ : Type} (f : α → β → γ) :
    f.swap.Injective2 ↔ f.Injective2 :=
  ⟨λ h _ _ _ _ h' ↦ and_comm.1 (h h'), λ h _ _ _ _ h' ↦ and_comm.1 (h h')⟩


/-- Summing `1` over list indices that satisfy a predicate is just `countP` applied to `p`. -/
lemma List.countP_eq_sum_fin_ite {α : Type} (xs : List α) (p : α → Bool) :
    (∑ i : Fin (xs.length), if p xs[i] then 1 else 0) = xs.countP p := by
  induction xs with
  | nil => simp only [List.countP_nil, List.length_nil, Finset.univ_eq_empty, Fin.getElem_fin,
      getElem?_eq_getElem, Fin.eta, Finset.sum_boole, Finset.filter_congr_decidable,
      Finset.not_mem_empty, IsEmpty.forall_iff, Finset.filter_true_of_mem, Finset.card_empty,
      CharP.cast_eq_zero]
  | cons y xs h => {
    rw [List.countP_cons]
    simp_rw [← h, length_cons]
    simp only [Nat.succ_eq_add_one, Fin.getElem_fin, getElem?_eq_getElem, length_cons, Fin.eta,
      Finset.sum_boole, Nat.cast_id]

    cases hp : p y
    · simp [h]

      -- rw [Multiset.countP_eq_card_filter]
      sorry
    · simp [h]
      sorry
      -- simp_rw [get_cons]
       }

@[simp]
lemma Vector.getElem_eq_get {α n} (xs : Vector α n) (i : ℕ) (h : i < n) :
  xs[i]'h = xs.get ⟨i, h⟩ := rfl
