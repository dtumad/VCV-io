/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.Seq
import ToMathlib.General

/-!
# Distribution Semantics for Lists and Vectors

This file collects various lemmas about the monadic sequence operation `og <*> oa`.

One especially important case is `f <$> oa <*> ob` where `f : α → β → γ`,
that runs the two computations `oa` and `ob` to get some `x` and `y` respectively,
returning only the value `f x y`.
-/

open Mathlib OracleSpec ENNReal BigOperators

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α β γ : Type}

section list

variable (oa : OracleComp spec α) (ob : OracleComp spec (List α))
  (x : α) (xs : List α)

lemma mem_support_seq_map_cons_iff' (xs : List α) : xs ∈ ((· :: ·) <$> oa <*> ob).support ↔
    xs.recOn False (λ x xs _ ↦ x ∈ oa.support ∧ xs ∈ ob.support) := by
  cases xs
  · simp only [support_seq_map_eq_image2, Set.mem_image2, and_false, exists_const, exists_false]
  · simp only [support_seq_map_eq_image2, Set.mem_image2, List.cons.injEq, exists_eq_right_right]

lemma mem_support_seq_map_cons_iff (xs : List α) (h : xs ≠ []) :
    xs ∈ ((· :: ·) <$> oa <*> ob).support ↔
      xs.head h ∈ oa.support ∧ xs.tail ∈ ob.support := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil h
  exact mem_support_seq_map_iff_of_injective2 oa ob _ List.injective2_cons _ _

lemma mem_finSupport_seq_map_cons_iff' [DecidableEq α] (xs : List α) :
    xs ∈ ((· :: ·) <$> oa <*> ob).finSupport ↔
      xs.recOn False (λ x xs _ ↦ x ∈ oa.finSupport ∧ xs ∈ ob.finSupport) := by
  simp_rw [mem_finSupport_iff_mem_support, mem_support_seq_map_cons_iff' oa ob xs]

lemma mem_finSupport_seq_map_cons_iff [DecidableEq α] (xs : List α) (h : xs ≠ []) :
    xs ∈ ((· :: ·) <$> oa <*> ob).finSupport ↔
      xs.head h ∈ oa.finSupport ∧ xs.tail ∈ ob.finSupport := by
  simp_rw [mem_finSupport_iff_mem_support, mem_support_seq_map_cons_iff oa ob xs h]

@[simp]
lemma probOutput_seq_map_cons_eq_mul :
    [= x :: xs | (· :: ·) <$> oa <*> ob] = [= x | oa] * [= xs | ob] :=
  probOutput_seq_map_eq_mul_of_injective2 oa ob List.cons List.injective2_cons x xs

@[simp]
lemma probOutput_seq_map_cons_eq_mul' :
    [= x :: xs | (λ xs x ↦ x :: xs) <$> ob <*> oa] = [= x | oa] * [= xs | ob] :=
  (probOutput_seq_map_swap oa ob (· :: ·) (x :: xs)).trans
    (probOutput_seq_map_cons_eq_mul oa ob x xs)

end list

section vector

variable {n : ℕ} (oa : OracleComp spec α) (ob : OracleComp spec (Vector α n))

@[simp]
lemma support_seq_map_vector_cons : ((· ::ᵥ ·) <$> oa <*> ob).support =
    {xs | xs.head ∈ oa.support ∧ xs.tail ∈ ob.support} := by
  refine Set.ext (λ xs ↦ ?_)
  simp [Set.ext_iff, @eq_comm _ _ xs, Vector.eq_cons_iff]

@[simp]
lemma probOutput_seq_map_vector_cons_eq_mul (xs : Vector α (n + 1)) :
    [= xs | (· ::ᵥ ·) <$> oa <*> ob] = [= xs.head | oa] * [= xs.tail | ob] := by
  rw [← probOutput_seq_map_eq_mul_of_injective2 oa ob _ Vector.injective2_cons,
    Vector.cons_head_tail]

@[simp]
lemma probOutput_seq_map_vector_cons_eq_mul' (xs : Vector α (n + 1)) :
    [= xs | (λ xs x ↦ x ::ᵥ xs) <$> ob <*> oa] = [= xs.head | oa] * [= xs.tail | ob] :=
  (probOutput_seq_map_swap oa ob (· ::ᵥ ·) (xs)).trans
    (probOutput_seq_map_vector_cons_eq_mul oa ob xs)

end vector
