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

open Mathlib OracleSpec OracleComp

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α β γ : Type}

section List

variable (oa : OracleComp spec α) (ob : OracleComp spec (List α))

lemma mem_support_seq_map_cons_iff' (xs : List α) : xs ∈ ((· :: ·) <$> oa <*> ob).support ↔
    xs.recOn False (λ x xs _ ↦ x ∈ oa.support ∧ xs ∈ ob.support) := by
  cases xs
  · simp [support_seq_map_eq_image2, Set.mem_image2, and_false, exists_const, exists_false]
  · simp only [support_seq_map_eq_image2, Set.mem_image2, List.cons.injEq, exists_eq_right_right]

lemma mem_support_seq_map_cons_iff (xs : List α) (h : xs ≠ []) :
    xs ∈ ((· :: ·) <$> oa <*> ob).support ↔
      xs.head h ∈ oa.support ∧ xs.tail ∈ ob.support := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil h
  exact mem_support_seq_map_iff_of_injective2 oa ob _ List.injective2_cons _ _

lemma cons_mem_support_seq_map_cons_iff (x : α) (xs : List α) :
    x :: xs ∈ ((· :: ·) <$> oa <*> ob).support ↔ x ∈ oa.support ∧ xs ∈ ob.support := by
  simp only [support_seq_map_eq_image2, Set.mem_image2, List.cons.injEq, exists_eq_right_right]

lemma mem_finSupport_seq_map_cons_iff' [spec.FiniteRange] [spec.DecidableSpec] [DecidableEq α]
    (xs : List α) : xs ∈ ((· :: ·) <$> oa <*> ob).finSupport ↔
      xs.recOn False (λ x xs _ ↦ x ∈ oa.finSupport ∧ xs ∈ ob.finSupport) := by
  simp_rw [mem_finSupport_iff_mem_support, mem_support_seq_map_cons_iff' oa ob xs]

lemma mem_finSupport_seq_map_cons_iff [spec.FiniteRange] [spec.DecidableSpec] [DecidableEq α]
    (xs : List α) (h : xs ≠ []) : xs ∈ ((· :: ·) <$> oa <*> ob).finSupport ↔
      xs.head h ∈ oa.finSupport ∧ xs.tail ∈ ob.finSupport := by
  simp_rw [mem_finSupport_iff_mem_support, mem_support_seq_map_cons_iff oa ob xs h]

lemma cons_mem_finSupport_seq_map_cons_iff [spec.FiniteRange] [spec.DecidableSpec] [DecidableEq α]
    (x : α) (xs : List α) : x :: xs ∈ ((· :: ·) <$> oa <*> ob).finSupport ↔
      x ∈ oa.finSupport ∧ xs ∈ ob.finSupport := by
  simp only [finSupport_seq_map_eq_image2, Finset.mem_image₂, List.cons.injEq,
    exists_eq_right_right]

lemma probOutput_cons_seq_map_cons_eq_mul [spec.FiniteRange] [spec.DecidableSpec] (x : α)
    (xs : List α) : [= x :: xs | (· :: ·) <$> oa <*> ob] = [= x | oa] * [= xs | ob] :=
  probOutput_seq_map_eq_mul_of_injective2 oa ob List.cons List.injective2_cons x xs

lemma probOutput_cons_seq_map_cons_eq_mul' [spec.FiniteRange] [spec.DecidableSpec] (x : α)
    (xs : List α) : [= x :: xs | (λ xs x ↦ x :: xs) <$> ob <*> oa] = [= x | oa] * [= xs | ob] :=
  (probOutput_seq_map_swap oa ob (· :: ·) (x :: xs)).trans
    (probOutput_cons_seq_map_cons_eq_mul oa ob x xs)

@[simp]
lemma probOutput_seq_map_cons_eq_mul [spec.FiniteRange] [spec.DecidableSpec] (xs : List α) :
    [= xs | (· :: ·) <$> oa <*> ob] = if h : xs.isEmpty then 0 else
      [= xs.head (h ∘ List.isEmpty_iff.2) | oa] * [= xs.tail | ob] :=
  match xs with
  | [] => by simp
  | x :: xs => probOutput_cons_seq_map_cons_eq_mul oa ob x xs

end List

section List.Vector

variable {n : ℕ} (oa : OracleComp spec α) (ob : OracleComp spec (List.Vector α n))

@[simp]
lemma support_seq_map_vector_cons : ((· ::ᵥ ·) <$> oa <*> ob).support =
    {xs | xs.head ∈ oa.support ∧ xs.tail ∈ ob.support} := by
  refine Set.ext (λ xs ↦ ?_)
  simp [Set.ext_iff, @eq_comm _ _ xs, List.Vector.eq_cons_iff]

@[simp]
lemma probOutput_seq_map_vector_cons_eq_mul [spec.FiniteRange] [spec.DecidableSpec]
    (xs : List.Vector α (n + 1)) :
    [= xs | (· ::ᵥ ·) <$> oa <*> ob] = [= xs.head | oa] * [= xs.tail | ob] := by
  rw [← probOutput_seq_map_eq_mul_of_injective2 oa ob _ Vector.injective2_cons,
    List.Vector.cons_head_tail]

@[simp]
lemma probOutput_seq_map_vector_cons_eq_mul' [spec.FiniteRange] [spec.DecidableSpec]
    (xs : List.Vector α (n + 1)) :
    [= xs | (λ xs x ↦ x ::ᵥ xs) <$> ob <*> oa] = [= xs.head | oa] * [= xs.tail | ob] :=
  (probOutput_seq_map_swap oa ob (· ::ᵥ ·) (xs)).trans
    (probOutput_seq_map_vector_cons_eq_mul oa ob xs)

@[simp]
lemma probOutput_vector_toList [spec.FiniteRange] [spec.DecidableSpec]
    {n : ℕ} (oa : OracleComp spec (List.Vector α n))
    (xs : List α) : [= xs | List.Vector.toList <$> oa] =
      if h : xs.length = n then [= ⟨xs, h⟩ | oa] else 0 := by
  split_ifs with h
  · refine probOutput_map_eq_single _ (λ _ _ h' ↦ List.Vector.eq ⟨xs, h⟩ _ h') rfl
  · simp only [probOutput_eq_zero_iff, support_map, Set.mem_image, not_exists, not_and]
    exact λ ys _ h' ↦ h (h' ▸ ys.toList_length)

end List.Vector

end OracleComp
