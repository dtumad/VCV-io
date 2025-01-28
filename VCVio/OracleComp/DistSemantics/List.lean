/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.Seq
import ToMathlib.General

/-!
# Distribution Semantics for Computations with Lists and Vectors

This file contains lemmas for `probEvent` and `probOutput` of computations involving `List`.
We also include `Vector` as a related case.
-/

open OracleSpec OracleComp List

universe u v w

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type v}

section List

variable (oa : OracleComp spec α) (ob : OracleComp spec (List α))

lemma mem_support_seq_map_cons_iff' (xs : List α) : xs ∈ (cons <$> oa <*> ob).support ↔
    xs.recOn False (λ x xs _ ↦ x ∈ oa.support ∧ xs ∈ ob.support) := by
  cases xs <;> simp

lemma mem_support_seq_map_cons_iff (xs : List α) (h : xs ≠ []) :
    xs ∈ (cons <$> oa <*> ob).support ↔
      xs.head h ∈ oa.support ∧ xs.tail ∈ ob.support := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil h
  simp [h]

lemma cons_mem_support_seq_map_cons_iff (x : α) (xs : List α) :
    x :: xs ∈ (cons <$> oa <*> ob).support ↔ x ∈ oa.support ∧ xs ∈ ob.support := by
  simp only [support_seq_map_eq_image2, Set.mem_image2, List.cons.injEq, exists_eq_right_right]

lemma mem_finSupport_seq_map_cons_iff' [spec.FiniteRange] [spec.DecidableEq] [DecidableEq α]
    (xs : List α) : xs ∈ (cons <$> oa <*> ob).finSupport ↔
      xs.recOn False (λ x xs _ ↦ x ∈ oa.finSupport ∧ xs ∈ ob.finSupport) := by
  simp_rw [mem_finSupport_iff_mem_support, mem_support_seq_map_cons_iff' oa ob xs]

lemma mem_finSupport_seq_map_cons_iff [spec.FiniteRange] [spec.DecidableEq] [DecidableEq α]
    (xs : List α) (h : xs ≠ []) : xs ∈ (cons <$> oa <*> ob).finSupport ↔
      xs.head h ∈ oa.finSupport ∧ xs.tail ∈ ob.finSupport := by
  simp_rw [mem_finSupport_iff_mem_support, mem_support_seq_map_cons_iff oa ob xs h]

lemma cons_mem_finSupport_seq_map_cons_iff [spec.FiniteRange] [spec.DecidableEq] [DecidableEq α]
    (x : α) (xs : List α) : x :: xs ∈ (cons <$> oa <*> ob).finSupport ↔
      x ∈ oa.finSupport ∧ xs ∈ ob.finSupport := by
  simp only [finSupport_seq_map_eq_image2, Finset.mem_image₂, List.cons.injEq,
    exists_eq_right_right]

lemma probOutput_cons_seq_map_cons_eq_mul [spec.FiniteRange] [spec.DecidableEq] (x : α)
    (xs : List α) : [= x :: xs | cons <$> oa <*> ob] = [= x | oa] * [= xs | ob] :=
  probOutput_seq_map_eq_mul_of_injective2 oa ob List.cons List.injective2_cons x xs

lemma probOutput_cons_seq_map_cons_eq_mul' [spec.FiniteRange] [spec.DecidableEq] (x : α)
    (xs : List α) : [= x :: xs | (λ xs x ↦ x :: xs) <$> ob <*> oa] = [= x | oa] * [= xs | ob] :=
  (probOutput_seq_map_swap oa ob cons (x :: xs)).trans
    (probOutput_cons_seq_map_cons_eq_mul oa ob x xs)

@[simp]
lemma probOutput_seq_map_cons_eq_mul [spec.FiniteRange] [spec.DecidableEq] (xs : List α) :
    [= xs | cons <$> oa <*> ob] = if h : xs.isEmpty then 0 else
      [= xs.head (h ∘ List.isEmpty_iff.2) | oa] * [= xs.tail | ob] :=
  match xs with
  | [] => by simp
  | x :: xs => probOutput_cons_seq_map_cons_eq_mul oa ob x xs

section append

@[simp]
lemma probOutput_map_append_left [DecidableEq α] [spec.FiniteRange] (xs : List α)
    (oa : OracleComp spec (List α)) (ys : List α) :
    [= ys | (xs ++ ·) <$> oa] = if ys.take xs.length = xs
      then [= ys.drop xs.length | oa] else 0 := by
  split_ifs with h
  · rw [probOutput_map_eq_tsum]
    refine (tsum_eq_single (drop xs.length ys) ?_).trans ?_
    · intro zs hzs
      simp
      intro h'
      rw [← h] at h'
      have := append_inj ((List.take_append_drop xs.length ys).trans h') rfl
      refine (hzs this.2.symm).elim
    · simp
      intro h'
      refine (h' ?_).elim
      refine ((List.take_append_drop xs.length ys)).symm.trans ?_
      refine congr_arg (· ++ _) h
  · simp
    intro x hx
    refine λ h' ↦ h ?_
    simp [← h', take_left']

end append

section mapM

@[simp]
lemma probFailure_list_mapM_loop [spec.FiniteRange]
    (xs : List α) (f : α → OracleComp spec β) (ys : List β) :
    [⊥ | List.mapM.loop f xs ys] = 1 - (xs.map (1 - [⊥ | f ·])).prod := by
  revert ys
  induction xs with
  | nil => {
    simp [List.mapM.loop]
  }
  | cons x xs h => {
    intros ys
    simp only [List.mapM.loop, List.map_cons, List.prod_cons]
    rw [probFailure_bind_eq_sub_mul (1 - (List.map (fun x ↦ 1 - [⊥|f x]) xs).prod)]
    · congr 2
      refine ENNReal.sub_sub_cancel ENNReal.one_ne_top ?_
      refine le_of_le_of_eq ?_ (one_pow (List.map (fun x ↦ 1 - [⊥|f x]) xs).length)
      exact List.prod_le_pow_card _ _ (by simp)
    · simp [h]
  }

@[simp]
lemma probFailure_list_mapM [spec.FiniteRange] (xs : List α) (f : α → OracleComp spec β) :
    [⊥ | xs.mapM f] = 1 - (xs.map (1 - [⊥ | f ·])).prod := by
  rw [mapM, probFailure_list_mapM_loop]

@[simp]
lemma probOutput_list_mapM_loop [DecidableEq β] [spec.FiniteRange]
    (xs : List α) (f : α → OracleComp spec β) (ys : List β)
    (zs : List β) : [= zs | List.mapM.loop f xs ys] =
      if zs.length = xs.length + ys.length ∧ zs.take ys.length = ys.reverse
      then (List.zipWith (λ x y ↦ [= y | f x]) xs zs).prod else 0 := by
  rw [list_mapM_loop_eq]
  rw [probOutput_map_append_left]
  by_cases h : take ys.length zs = ys.reverse
  · simp only [length_reverse, h, ↓reduceIte, and_true]
    induction zs using List.reverseRecOn with
    | nil => {
      simp at h
      simp [h]
      cases xs with
      | nil => {
        simp [mapM.loop]
      }
      | cons x xs => {
        simp [mapM.loop]
        intro _ _
        rw [list_mapM_loop_eq]
        simp
      }
    }
    | append_singleton zs z hzs => {
      cases xs with
      | nil => {
        suffices zs.length + 1 ≤ ys.length ↔ zs.length + 1 = ys.length
        by simp [mapM.loop, this]
        refine LE.le.le_iff_eq ?_
        simpa using congr_arg length h
      }
      | cons x xs => {
        simp [Nat.succ_add, mapM.loop]
        sorry
      }
    }
  · simp [h]

@[simp]
lemma probOutput_list_mapM [spec.FiniteRange] (xs : List α) (f : α → OracleComp spec β)
    (ys : List β) : [= ys | xs.mapM f] = if ys.length = xs.length
      then (List.zipWith (λ x y ↦ [= y | f x]) xs ys).prod else 0 := by
  have : DecidableEq β := Classical.decEq β; simp [List.mapM]

end mapM

end List

section List.Vector

variable {n : ℕ} (oa : OracleComp spec α) (ob : OracleComp spec (List.Vector α n))

@[simp]
lemma support_seq_map_vector_cons : ((· ::ᵥ ·) <$> oa <*> ob).support =
    {xs | xs.head ∈ oa.support ∧ xs.tail ∈ ob.support} := by
  refine Set.ext (λ xs ↦ ?_)
  simp [Set.ext_iff, @eq_comm _ _ xs, List.Vector.eq_cons_iff]

@[simp]
lemma probOutput_seq_map_vector_cons_eq_mul [spec.FiniteRange] [spec.DecidableEq]
    (xs : List.Vector α (n + 1)) :
    [= xs | (· ::ᵥ ·) <$> oa <*> ob] = [= xs.head | oa] * [= xs.tail | ob] := by
  rw [← probOutput_seq_map_eq_mul_of_injective2 oa ob _ Vector.injective2_cons,
    List.Vector.cons_head_tail]

@[simp]
lemma probOutput_seq_map_vector_cons_eq_mul' [spec.FiniteRange] [spec.DecidableEq]
    (xs : List.Vector α (n + 1)) :
    [= xs | (λ xs x ↦ x ::ᵥ xs) <$> ob <*> oa] = [= xs.head | oa] * [= xs.tail | ob] :=
  (probOutput_seq_map_swap oa ob (· ::ᵥ ·) (xs)).trans
    (probOutput_seq_map_vector_cons_eq_mul oa ob xs)

@[simp]
lemma probOutput_vector_toList [spec.FiniteRange] [spec.DecidableEq]
    {n : ℕ} (oa : OracleComp spec (List.Vector α n))
    (xs : List α) : [= xs | List.Vector.toList <$> oa] =
      if h : xs.length = n then [= ⟨xs, h⟩ | oa] else 0 := by
  split_ifs with h
  · refine probOutput_map_eq_single _ (λ _ _ h' ↦ List.Vector.eq ⟨xs, h⟩ _ h') rfl
  · simp only [probOutput_eq_zero_iff, support_map, Set.mem_image, not_exists, not_and]
    exact λ ys _ h' ↦ h (h' ▸ ys.toList_length)

end List.Vector

end OracleComp
