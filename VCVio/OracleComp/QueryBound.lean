/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.QueryTracking.CountingOracle

/-!
# Bounding Queries Made by a Computation

This file defines a predicate `IsQueryBound oa qb` to say that a computation with oracles `spec`
never makes a larger number of queries than is given by a bound `qb : spec.ι → ℕ`.
This is useful for showing that some simulated computation is polynomial time,
and in things like seeding query values for a computation.
-/

open OracleSpec Prod

namespace OracleComp

section IsQueryBound

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} {α β γ : Type}

/-- Bound on the number of queries made by a computation, given by a map from oracles to counts. -/
def IsQueryBound (oa : OracleComp spec α) (qb : ι → ℕ) : Prop :=
    ∀ qc ∈ (snd <$> simulate countingOracle 0 oa).support, qc ≤ qb

lemma isQueryBound_def (oa : OracleComp spec α) (qb : ι → ℕ) : IsQueryBound oa qb ↔
    ∀ qc ∈ (snd <$> simulate countingOracle 0 oa).support, qc ≤ qb := Iff.rfl

@[simp]
lemma isQueryBound_pure (a : α) (qb : ι → ℕ) :
    IsQueryBound (pure a : OracleComp spec α) qb := by
  simp [isQueryBound_def]

@[simp]
lemma isQueryBound_query_iff (i : ι) (t : spec.domain i) (qb : ι → ℕ) :
    IsQueryBound (query i t) qb ↔ 0 < qb i := by
  simp [isQueryBound_def, Nat.lt_iff_add_one_le, zero_add]
  refine ⟨λ h ↦ le_of_eq_of_le (symm <| Function.update_same i 1 0) (h i), λ h j ↦ ?_⟩
  by_cases hij : j = i
  · induction hij
    simpa using h
  · simp [Function.update_noteq hij]

lemma isQueryBound_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β) (qb₁ qb₂ : ι → ℕ)
    (h1 : IsQueryBound oa qb₁) (h2 : ∀ x, IsQueryBound (ob x) qb₂) :
    IsQueryBound (oa >>= ob) (qb₁ + qb₂) := by
  intros count h
  simp at h
  obtain ⟨y, x, count', h, h'⟩ := h
  specialize h1 count'
  rw [support_map] at h1
  have : count' ≤ count := sorry
  specialize h1 ⟨⟨x, count'⟩, h, rfl⟩
  specialize h2 x (count - count') sorry
  have h3 := add_le_add h2 h1
  rw [add_comm qb₂] at h3
  refine le_trans ?_ h3
  intros x
  specialize this x
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [tsub_add_cancel_of_le this]

@[simp]
lemma isQueryBound_map_iff (oa : OracleComp spec α) (f : α → β) (qb : ι → ℕ) :
    IsQueryBound (f <$> oa) qb ↔ IsQueryBound oa qb := by
  simp [isQueryBound_def]

end IsQueryBound

section PolyQueries

structure PolyQueries {ι : Type} [DecidableEq ι] {spec : ℕ → OracleSpec ι}
  {α β : ℕ → Type} (oa : (n : ℕ) → α n → OracleComp (spec n) (β n)) where
  qb : ι → Polynomial ℕ
  qb_isQueryBound (n : ℕ) (x : α n) :
    IsQueryBound (oa n x) (λ i ↦ (qb i).eval n)

end PolyQueries

end OracleComp
