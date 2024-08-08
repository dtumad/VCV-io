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

lemma isQueryBound_def (oa : OracleComp spec α) (qb : ι → ℕ) :
    IsQueryBound oa qb ↔ ∀ qc ∈ (snd <$> simulate countingOracle 0 oa).support, qc ≤ qb := Iff.rfl

lemma isQueryBound_mono {oa : OracleComp spec α} {qb qb' : ι → ℕ}
    (h' : IsQueryBound oa qb) (h : qb ≤ qb') : IsQueryBound oa qb' := by
  intro qc hqc
  specialize h' qc hqc
  refine le_trans h' h

@[simp]
lemma isQueryBound_pure (a : α) (qb : ι → ℕ) :
    IsQueryBound (pure a : OracleComp spec α) qb := by
  simp [isQueryBound_def]

@[simp]
lemma isQueryBound_query_iff (i : ι) (t : spec.domain i) (qb : ι → ℕ) :
    IsQueryBound (query i t) qb ↔ qb i ≠ 0 := by
  simp [isQueryBound_def, Nat.lt_iff_add_one_le, zero_add, ← Nat.pos_iff_ne_zero]
  refine ⟨λ h ↦ le_of_eq_of_le (symm <| Function.update_same i 1 0) (h i), λ h j ↦ ?_⟩
  by_cases hij : j = i
  · induction hij
    simpa using h
  · simp [Function.update_noteq hij]

lemma isQueryBound_query (i : ι) (t : spec.domain i) {qb : ι → ℕ} (hqb : qb i ≠ 0) :
    IsQueryBound (query i t) qb :=
  (isQueryBound_query_iff i t qb).2 hqb

lemma update_isQueryBound_query (i : ι) (t : spec.domain i) :
    IsQueryBound (query i t) (Function.update 0 i 1) := by
  refine isQueryBound_query i t ?_
  simp only [Function.update_same, ne_eq, one_ne_zero, not_false_eq_true]

lemma isQueryBound_bind {oa : OracleComp spec α} {ob : α → OracleComp spec β} {qb₁ qb₂ : ι → ℕ}
    (h1 : IsQueryBound oa qb₁) (h2 : ∀ x, IsQueryBound (ob x) qb₂) :
    IsQueryBound (oa >>= ob) (qb₁ + qb₂) := by
  intros count h
  simp at h
  obtain ⟨y, x, count', h, h'⟩ := h
  specialize h1 count'
  rw [support_map] at h1
  have : count' ≤ count := countingOracle.le_of_mem_support_simulate h'
  specialize h1 ⟨⟨x, count'⟩, h, rfl⟩
  specialize h2 x (count - count') (by {
    rw [← countingOracle.mem_support_snd_map_simulate_iff_of_le _ this,
      support_map, Set.mem_image] -- TODO: shouldn't need two steps
    refine ⟨(y, count), h', rfl⟩
  })
  have h3 := add_le_add h2 h1
  rw [add_comm qb₂] at h3
  refine le_trans ?_ h3
  intros x
  specialize this x
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [tsub_add_cancel_of_le this]

section minimalQueryBound

/-- The minimal query bound on a computation. Note that this is noncomputatble,
since we need to take a minimum over the entire codomain at each query step. -/
def minimalQueryBound : {α : Type} → OracleComp spec α → (ι → ℕ)
  | _, pure' _ _ => 0
  | _, queryBind' i _ _ oa => λ j ↦ (if j = i then 1 else 0) +
      (Finset.max' (Finset.univ.image <| λ u ↦ minimalQueryBound (oa u) j)
        (by simpa using Finset.univ_nonempty))

lemma isQueryBound_minimalQueryBound (oa : OracleComp spec α) :
    IsQueryBound oa (minimalQueryBound oa) := by
  induction oa using OracleComp.inductionOn with
  | h_pure x => exact isQueryBound_pure x _
  | h_queryBind i t oa hoa =>
    · refine isQueryBound_bind (by simp) <| λ u ↦ isQueryBound_mono (hoa u)
        (λ j ↦ Finset.le_max' _ _ ?_)
      simp only [OracleComp.bind'_eq_bind, pure_bind, Finset.mem_image, Finset.mem_univ, true_and,
        exists_apply_eq_apply]

lemma minimalQueryBound_mem_support_simulate (oa : OracleComp spec α) :
    minimalQueryBound oa ∈ (snd <$> simulate countingOracle 0 oa).support := by
  induction oa using OracleComp.inductionOn with
  | h_pure x => rfl
  | h_queryBind i t oa hoa => {
    simp only [minimalQueryBound]
    sorry
  }

lemma minimalQueryBound_minimal (oa : OracleComp spec α) :
    Minimal (IsQueryBound oa) (minimalQueryBound oa) := by
  rw [minimal_iff]
  refine ⟨isQueryBound_minimalQueryBound oa, ?_⟩
  sorry

lemma le_minimalQueryBound_of_isQueryBound {oa : OracleComp spec α} (qc : ι → ℕ)
    (hqc : IsQueryBound oa qc) : minimalQueryBound oa ≤ qc := by
  induction oa using OracleComp.inductionOn with
  | h_pure x => {
    exact zero_le _
  }
  | h_queryBind i t oa hoa => {
    simp only [minimalQueryBound]
    intro j
    by_cases hj : j = i
    · induction hj
      simp only [↓reduceIte, OracleComp.bind'_eq_bind, pure_bind]
      sorry
    · simp [hj]
      sorry
  }

lemma exists_isQueryBound (oa : OracleComp spec α) : ∃ qc, IsQueryBound oa qc :=
  ⟨minimalQueryBound oa, isQueryBound_minimalQueryBound oa⟩

lemma exists_minimal_isQueryBound (oa : OracleComp spec α) :
    ∃ qc, IsQueryBound oa qc ∧ (∀ qc', IsQueryBound oa qc' → qc ≤ qc') := by
  refine ⟨minimalQueryBound oa, isQueryBound_minimalQueryBound oa,
    le_minimalQueryBound_of_isQueryBound⟩

end minimalQueryBound

lemma isQueryBound_query_bind_iff (i : ι) (t : spec.domain i)
    (oa : spec.range i → OracleComp spec α) (qc : ι → ℕ) :
    IsQueryBound (query i t >>= oa) qc ↔ qc i ≠ 0 ∧
      ∀ u, IsQueryBound (oa u) (Function.update qc i (qc i - 1)) := by
  refine ⟨λ h ↦ ⟨?_, ?_⟩, λ h ↦ ?_⟩
  · specialize h (minimalQueryBound (query i t >>= oa))
    sorry
  · sorry
  · refine isQueryBound_mono (isQueryBound_bind (update_isQueryBound_query i t) h.2) ?_
    intro j
    by_cases hj : j = i
    · simp only [hj, Pi.add_apply, Function.update_same]
      rw [Nat.add_sub_of_le]
      rw [Nat.one_le_iff_ne_zero]
      exact h.1
    · simp [hj]

@[simp]
lemma isQueryBound_map_iff (oa : OracleComp spec α) (f : α → β) (qb : ι → ℕ) :
    IsQueryBound (f <$> oa) qb ↔ IsQueryBound oa qb := by
  simp [isQueryBound_def]

-- isQueryBound_seq_iff

section simulate

variable {ι' : Type} {spec' : OracleSpec ι} {σ : Type}

/-- If we have a query bound on a computation, and a query bound on a `SimOracle` implementation,
then their product is a query bound on the -/
lemma isQueryBound_simulate (oa : OracleComp spec α) (so : spec →[σ]ₛₒ spec') (s : σ)
    {qb qbs : ι → ℕ} (hqb : IsQueryBound oa qb) (hqbs : ∀ i t s, IsQueryBound (so i t s) qbs) :
    IsQueryBound (simulate so s oa) (qb * qbs) := by
  induction oa using OracleComp.inductionOn with
  | h_pure x => exact isQueryBound_pure (x, s) (qb * qbs)
  | h_queryBind i t oa hoa => {
      rw [simulate_query_bind]
      sorry
  }

end simulate


-- @[simp] -- TODO: isPure predicate?
-- lemma zero_isQueryBound_iff (oa : OracleComp spec α) :
--     IsQueryBound oa 0 ↔ ∃ x, oa = pure x := by
--   refine ⟨λ h ↦ ?_, λ ⟨x, hx⟩ ↦ hx ▸ isQueryBound_pure x 0⟩
--   induction oa using OracleComp.inductionOn with
--   | h_pure x => exact ⟨x, rfl⟩
--   | h_queryBind i t oa hoa => {
--     simp
--     specialize h (minimalQueryBound (query i t >>= oa)) ?_
--     ·
--       sorry
--     · specialize h i
--       simp [minimalQueryBound] at h


--   }

end IsQueryBound

section PolyQueries

structure PolyQueries {ι : Type} [DecidableEq ι] {spec : ℕ → OracleSpec ι}
  {α β : ℕ → Type} (oa : (n : ℕ) → α n → OracleComp (spec n) (β n)) where
  qb : ι → Polynomial ℕ
  qb_isQueryBound (n : ℕ) (x : α n) :
    IsQueryBound (oa n x) (λ i ↦ (qb i).eval n)

end PolyQueries

end OracleComp
