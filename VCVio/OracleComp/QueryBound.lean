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

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} {α : Type}

/-- Bound on the number of queries made by a computation, given by a map from oracles to counts. -/
def IsQueryBound (oa : OracleComp spec α) (qb : ι → ℕ) : Prop :=
    ∀ count ∈ (snd <$> simulate countingOracle 0 oa).support, count ≤ qb

lemma isQueryBound_def (oa : OracleComp spec α) (qb : ι → ℕ) : IsQueryBound oa qb ↔
    ∀ count ∈ (snd <$> simulate countingOracle 0 oa).support, count ≤ qb := Iff.rfl

lemma isQueryBound_query_iff (i : ι) (t : spec.domain i) (qb : ι → ℕ) :
    IsQueryBound (query i t) qb ↔ 0 < qb i := by
  simp [isQueryBound_def, Nat.lt_iff_add_one_le, zero_add]
  refine ⟨?_, ?_⟩
  · intro h
    specialize h i
    rwa [Function.update_same] at h
  · intro h
    intro j
    by_cases hij : j = i
    · induction hij
      simpa using h
    · simp [Function.update_noteq hij]

end IsQueryBound

section PolyQueries

structure PolyQueries {ι : Type} [DecidableEq ι] {spec : ℕ → OracleSpec ι}
  {α β : ℕ → Type} (oa : (n : ℕ) → α n → OracleComp (spec n) (β n)) where
  qb : ι → Polynomial ℕ
  qb_isQueryBound (n : ℕ) (x : α n) :
    IsQueryBound (oa n x) (λ i ↦ (qb i).eval n)

end PolyQueries

end OracleComp
