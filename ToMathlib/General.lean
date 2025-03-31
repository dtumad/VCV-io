/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Vector.Defs
import Mathlib.Probability.Distributions.Uniform

/-!
# Lemmas to be Ported to Mathlib

This file gives a centralized location to add lemmas that belong better
in general mathlib than in the project itself.
-/

universe u v w

open List (Vector)
open BigOperators ENNReal

lemma Fintype.sum_inv_card (α : Type*) [Fintype α] [Nonempty α] :
  Finset.sum Finset.univ (λ _ ↦ (Fintype.card α)⁻¹ : α → ℝ≥0∞) = 1 := by
  rw [Finset.sum_eq_card_nsmul (λ _ _ ↦ rfl), Finset.card_univ,
    nsmul_eq_mul, ENNReal.mul_inv_cancel] <;> simp

@[simp] -- mathlib?
lemma vector_eq_nil {α : Type*} (xs : List.Vector α 0) : xs = Vector.nil :=
  List.Vector.ext (IsEmpty.forall_iff.2 True.intro)

lemma List.injective2_cons {α : Type*} : Function.Injective2 (List.cons (α := α)) := by
  simp [Function.Injective2]

lemma Vector.injective2_cons {α : Type*} {n : ℕ} :
    Function.Injective2 (Vector.cons : α → List.Vector α n → List.Vector α (n + 1)) := by
  simp [Function.Injective2, Vector.eq_cons_iff]

lemma Prod.mk.injective2 {α β : Type*} :
    Function.Injective2 (Prod.mk : α → β → α × β) := by
  simp [Function.Injective2]

lemma Function.injective2_swap_iff {α β γ : Type*} (f : α → β → γ) :
    f.swap.Injective2 ↔ f.Injective2 :=
  ⟨λ h _ _ _ _ h' ↦ and_comm.1 (h h'), λ h _ _ _ _ h' ↦ and_comm.1 (h h')⟩

@[simp] theorem Finset.image_const_univ {α β} [DecidableEq β]  [Fintype α]
    [Nonempty α] (b : β) : (Finset.univ.image fun _ : α => b) = singleton b :=
  Finset.univ.image_const Finset.univ_nonempty b

/-- Summing `1` over list indices that satisfy a predicate is just `countP` applied to `p`. -/
lemma List.countP_eq_sum_fin_ite {α : Type*} (xs : List α) (p : α → Bool) :
    (∑ i : Fin xs.length, if p xs[i] then 1 else 0) = xs.countP p := by
  induction xs with
  | nil => {
    simp only [length_nil, Finset.univ_eq_empty, Finset.sum_boole, Fin.getElem_fin,
      Finset.filter_empty, Finset.card_empty, CharP.cast_eq_zero, countP_nil]
  }
  | cons x xs h => {
    rw [List.countP_cons, ← h]
    refine (Fin.sum_univ_succ _).trans ((add_comm _ _).trans ?_)
    simp
  }

lemma List.card_filter_getElem_eq {α : Type*} [DecidableEq α]
    (xs : List α) (x : α) :
    (Finset.filter (λ i : Fin (xs.length) ↦ xs[i] = x) Finset.univ).card =
      xs.count x := by
  rw [List.count, ← List.countP_eq_sum_fin_ite]
  simp only [Fin.getElem_fin, beq_iff_eq, Finset.sum_boole, Nat.cast_id]

@[simp]
lemma Vector.getElem_eq_get {α n} (xs : List.Vector α n) (i : ℕ) (h : i < n) :
  xs[i]'h = xs.get ⟨i, h⟩ := rfl

@[simp] lemma Finset.sum_boole' {ι β : Type*} [AddCommMonoid β] (r : β)
    (p) [DecidablePred p] (s : Finset ι) :
    (∑ x ∈ s, if p x then r else 0 : β) = (s.filter p).card • r :=
calc (∑ x ∈ s, if p x then r else 0 : β) = (∑ x ∈ s, if p x then 1 else 0 : ℕ) • r :=
    by simp only [← Finset.sum_nsmul_assoc, ite_smul, one_smul, zero_smul]
  _ = (s.filter p).card • r := by simp only [sum_boole, Nat.cast_id]

@[simp]
lemma Finset.count_toList {α} [DecidableEq α] (x : α) (s : Finset α) :
    s.toList.count x = if x ∈ s then 1 else 0 := by
  by_cases hx : x ∈ s
  · simp [hx]
    refine List.count_eq_one_of_mem ?_ ?_
    · exact nodup_toList s
    · simp [hx]
  · simp [hx]
    refine List.count_eq_zero_of_not_mem ?_
    simp [hx]

lemma BitVec.toFin_bijective (n : ℕ) :
    Function.Bijective (BitVec.toFin : BitVec n → Fin (2 ^ n)) := by
  refine ⟨?_, ?_⟩
  · intro i j h
    cases i
    cases j
    simp at h
    simp [h]
  · intro i
    simp only [exists_apply_eq_apply]

instance (n : ℕ) : Fintype (BitVec n) := by
  refine Fintype.ofBijective (α := Fin (2 ^ n)) ?_ ?_
  · refine λ x ↦ ?_
    refine BitVec.ofFin x
  · refine ⟨?_, ?_⟩
    · intro i j
      simp only [BitVec.ofFin.injEq, imp_self]
    · intro i
      simp only [exists_apply_eq_apply]

@[simp]
lemma card_bitVec (n : ℕ) : Fintype.card (BitVec n) = 2 ^ n :=
  (Fintype.card_of_bijective (BitVec.toFin_bijective _)).trans <| Fintype.card_fin (2 ^ n)

@[simp]
lemma BitVec.xor_self_xor {n : ℕ} (x y : BitVec n) : x ^^^ (x ^^^ y) = y := by
  rw [← BitVec.xor_assoc, xor_self, zero_xor]

instance (α : Type) [Inhabited α] : Inhabited {f : α → α // f.Bijective} :=
  ⟨id, Function.bijective_id⟩

open Classical

lemma tsum_option {α β : Type*} [AddCommMonoid α] [TopologicalSpace α]
    [ContinuousAdd α] [T2Space α]
    (f : Option β → α) (hf : Summable (Function.update f none 0)) :
    ∑' x : Option β, f x = f none + ∑' x : β, f (some x) := by
  refine (tsum_eq_add_tsum_ite' none hf).trans ?_
  refine congr_arg (f none + ·) ?_
  refine tsum_eq_tsum_of_ne_zero_bij (λ x ↦ some x.1) ?_ ?_ ?_
  · intro x y
    simp [SetCoe.ext_iff]
  · intro x
    cases x <;> simp
  · simp

@[simp]
lemma PMF.monad_pure_eq_pure {α : Type u} (x : α) :
    (Pure.pure x : PMF α) = PMF.pure x := rfl

@[simp]
lemma PMF.monad_bind_eq_bind {α β : Type u}
      (p : PMF α) (q : α → PMF β) : p >>= q = p.bind q := rfl

@[simp]
lemma List.foldlM_range {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {s : Type u} (n : ℕ) (f : s → Fin n → m s) (init : s)  :
    List.foldlM f init (List.finRange n) =
      Fin.foldlM n f init := by
  revert init
  induction n with
  | zero => simp
  | succ n hn =>
      intro init
      simp only [List.finRange_succ, List.foldlM_cons, Fin.foldlM_succ]
      refine congr_arg (_ >>= ·) (funext λ x ↦ ?_)
      rw [← hn, List.foldlM_map]

lemma list_mapM_loop_eq {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {α : Type w} {β : Type u} (xs : List α) (f : α → m β) (ys : List β) :
    List.mapM.loop f xs ys = (ys.reverse ++ ·) <$> List.mapM.loop f xs [] := by
  revert ys
  induction xs with
  | nil => simp [List.mapM.loop]
  | cons x xs h =>
      intro ys
      simp only [List.mapM.loop, map_bind]
      refine congr_arg (f x >>= ·) (funext λ x ↦ ?_)
      simp [h (x :: ys), h [x]]
