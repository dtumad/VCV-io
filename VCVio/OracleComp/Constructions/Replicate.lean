/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Constructions.UniformSelect
import VCVio.OracleComp.DistSemantics.Seq
import VCVio.OracleComp.DistSemantics.List
import Init.Data.Vector.Lemmas

/-!
# Running a Computation Multiple Times

This file defines a function `replicate oa n` that runs the computation `oa` a total of `n` times,
returning the result as a list of length `n`.

Note that while the executions are independent, they may no longer be after calling `simulate`.
-/


open OracleSpec Vector

namespace OracleComp

#check probFailure_bind_of_const

open ENNReal

@[simp]
lemma probFailure_list_mapM_loop {ι : Type} {spec : OracleSpec ι} [spec.FiniteRange] {α β : Type}
    -- [Nonempty β]
    (xs : List α) (f : α → OracleComp spec β) (ys : List β) :
    [⊥ | List.mapM.loop f xs ys] = 1 - (xs.map (1 - [⊥ | f ·])).prod := by
  revert ys
  induction xs with
  | nil => {
    simp [List.mapM.loop]
  }
  | cons x xs h => {
    -- simp []
    intros ys
    rw [List.mapM.loop]
    simp only [List.map_cons, List.prod_cons]
    rw [probFailure_bind_eq_sub_mul (1 - (List.map (fun x ↦ 1 - [⊥|f x]) xs).prod)]
    · congr
      refine ENNReal.sub_sub_cancel one_ne_top ?_
      refine le_of_le_of_eq ?_ (one_pow (List.map (fun x ↦ 1 - [⊥|f x]) xs).length)
      apply List.prod_le_pow_card _ _ _
      simp
    · simp [h]
  }

@[simp]
lemma probFailure_list_mapM {ι : Type} {spec : OracleSpec ι} [spec.FiniteRange] {α β : Type}
    (xs : List α) (f : α → OracleComp spec β) :
    [⊥ | xs.mapM f] = 1 - (xs.map (1 - [⊥ | f ·])).prod := by
  rw [mapM, probFailure_list_mapM_loop]

@[simp]
lemma probOutput_list_mapM {ι : Type} {spec : OracleSpec ι} [spec.FiniteRange] {α β : Type}
    (xs : List α) (f : α → OracleComp spec β) (ys : List β) :
    [= ys | xs.mapM f] = if ys.length = xs.length then
      (List.zipWith (λ x y ↦ [= y | f x]) xs ys).prod else 0 := by
  sorry

/-- Run the computation `oa` repeatedly `n` times to get a vector of `n` results. -/
def replicate {ι : Type} {spec : OracleSpec ι} {α : Type}
    (n : ℕ) (oa : OracleComp spec α) : OracleComp spec (List α) := do
  (List.replicate n ()).mapM (λ () ↦ oa)

def replicateTR {ι : Type} {spec : OracleSpec ι} {α : Type}
    (n : ℕ) (oa : OracleComp spec α) : OracleComp spec (List α) := do
  (List.replicateTR n ()).mapM (λ () ↦ oa)

variable {ι : Type} {spec : OracleSpec ι} {α β : Type} (oa : OracleComp spec α)

@[simp]
lemma replicate_zero (oa : OracleComp spec α) :
    replicate 0 oa = return [] := rfl

@[simp]
lemma replicate_succ (oa : OracleComp spec α) (n : ℕ) :
    replicate (n + 1) oa = List.cons <$> oa <*> replicate n oa := by
  rw [replicate, List.replicate_succ, List.mapM_cons, seq_eq_bind, bind_map_left]; rfl

@[simp]
lemma replicate_pure (x : α) (n : ℕ) :
    (pure x : OracleComp spec α).replicate n = pure (List.replicate n x) := by
  induction n with
  | zero => rfl
  | succ n hn => simp [hn, List.replicate]

@[simp]
lemma probFailure_replicate [spec.FiniteRange] (oa : OracleComp spec α) (n : ℕ) :
    [⊥ | oa.replicate n] = 1 - (1 - [⊥ | oa]) ^ n := by
  rw [replicate, probFailure_list_mapM, List.map_replicate, List.prod_replicate]

/-- The probability of getting a vector from `replicate` is the product of the chances of
getting each of the individual elements. -/
@[simp]
lemma probOutput_replicate [spec.FiniteRange] (oa : OracleComp spec α) (n : ℕ) (xs : List α) :
    [= xs | oa.replicate n] = if xs.length = n then (xs.map ([= · | oa])).prod else 0 := by
  rw [replicate, probOutput_list_mapM, List.length_replicate]
  split_ifs with hxs
  · exact congr_arg List.prod <| List.ext_getElem (by simp [hxs]) (by simp)
  · rfl

lemma probEvent_of_probEvent_cons [spec.FiniteRange] (oa : OracleComp spec α) (n : ℕ)
    (p : List α → Prop) (hp : p [])
    (q : α → Prop) (hq : ∀ x xs, p (x :: xs) ↔ q x ∧ p xs) :
    [p | oa.replicate n] = [q | oa] ^ n := by
  induction n with
  | zero => {
    simpa using hp
  }
  | succ n hn => {
    simp [pow_succ, ← hn]

    sorry
  }

@[simp]
lemma probEvent_all_replicate [spec.FiniteRange] (oa : OracleComp spec α) (n : ℕ) (p : α → Bool) :
    [λ xs ↦ List.all xs p | oa.replicate n] = [λ x ↦ p x | oa] ^ n := by
  induction n with
  | zero => {
    simp
  }
  | succ n hn => {
    simp [pow_succ, ← hn]

    sorry
  }

lemma support_eq_setOf_probOutput_eq_zero [spec.FiniteRange] (oa : OracleComp spec α) :
    oa.support = {x | [= x | oa] ≠ 0} := by
  simp only [ne_eq, probOutput_eq_zero_iff, not_not, Set.setOf_mem_eq]

/-- Possible ouptuts of `replicate n oa` are lists of length `n` where
ecah element in the list is a possible output of `oa`. -/
@[simp]
lemma support_replicate [spec.FiniteRange] (oa : OracleComp spec α) (n : ℕ) :
    (oa.replicate n).support = {xs | xs.length = n ∧ ∀ x ∈ xs, x ∈ oa.support} := by
  rw [support_eq_setOf_probOutput_eq_zero]; simp

/-- Version of `support_replicate` using `List.all` instead of quantifiers.
Requires decidable equality on the output type of the computation. -/
lemma support_replicate' [spec.FiniteRange] [DecidableEq α] (oa : OracleComp spec α) (n : ℕ) :
    (oa.replicate n).support = {xs | xs.length = n ∧ xs.all (· ∈ oa.support)} := by
  simp only [support_replicate, List.all_eq_true, decide_eq_true_eq]

@[simp]
lemma mem_finSupport_replicate [spec.FiniteRange] [spec.DecidableSpec] [DecidableEq α]
    (oa : OracleComp spec α) (n : ℕ)
    (xs : List α) : xs ∈ (oa.replicate n).finSupport ↔
      xs.length = n ∧ xs.all (· ∈ oa.finSupport) := by
  simp [mem_finSupport_iff_mem_support]

-- section SelectableTypeVector

-- /-- Vectors can be selected uniformly if the underlying type can be.
-- Note: this isn't very efficient as an actual implementation in practice. -/
-- instance (α : Type) [Fintype α] [Inhabited α] [SelectableType α] (n : ℕ) :
--     SelectableType (Vector α n) where
--   selectElem := _ <$> ($ᵗ α).replicate n
--   probOutput_selectElem_eq xs ys := by simp
--   probFailure_selectElem := by simp

-- end SelectableTypeVector

end OracleComp
