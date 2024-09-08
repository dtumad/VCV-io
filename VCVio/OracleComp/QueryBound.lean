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

We also define a function `minimalQueryBound oa` that returns the smallest such count.
Calculating this is generally expensive, and so it shouldn't be used in actual algorithms,
but it can be useful in some proofs that only care about the existence of a bound.
-/

open OracleSpec Prod

namespace OracleComp

section IsQueryBound

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} {α β γ : Type}

/-- Predicate expressing that `qb` is a bound on the number of queries made by `oa`.
In particular any simulation with a `countingOracle` produces counts that are smaller. -/
def IsQueryBound (oa : OracleComp spec α) (qb : ι → ℕ) : Prop :=
    ∀ qc ∈ (snd <$> simulate countingOracle 0 oa).support, qc ≤ qb

lemma isQueryBound_def (oa : OracleComp spec α) (qb : ι → ℕ) :
    IsQueryBound oa qb ↔ ∀ qc ∈ (snd <$> simulate countingOracle 0 oa).support, qc ≤ qb :=
  Iff.rfl

lemma isQueryBound_mono {oa : OracleComp spec α} (qb : ι → ℕ) {qb' : ι → ℕ}
    (h' : IsQueryBound oa qb) (h : qb ≤ qb') : IsQueryBound oa qb' :=
  λ qc hqc ↦ le_trans (h' qc hqc) h

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
    (h1 : IsQueryBound oa qb₁) (h2 : ∀ x ∈ oa.support, IsQueryBound (ob x) qb₂) :
    IsQueryBound (oa >>= ob) (qb₁ + qb₂) := by
  intros count h
  simp at h
  obtain ⟨y, x, count', h, h'⟩ := h
  specialize h1 count'
  rw [support_map] at h1
  have : count' ≤ count := countingOracle.le_of_mem_support_simulate h'
  have hxoa : x ∈ oa.support := by {
    have := mem_support_simulate'_of_mem_support_simulate _ _ h
    simp at this
    exact this
  }
  specialize h1 ⟨⟨x, count'⟩, h, rfl⟩
  specialize h2 x hxoa (count - count') (by {
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

lemma isQueryBound_query_bind_iff (i : ι) (t : spec.domain i)
    (oa : spec.range i → OracleComp spec α) (qb : ι → ℕ) :
    IsQueryBound (query i t >>= oa) qb ↔
      qb i ≠ 0 ∧ ∀ u, IsQueryBound (oa u) (Function.update qb i (qb i - 1)) := by
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · sorry
  · sorry

section minimalQueryBound

/-- The minimal query bound on a computation, assuming that at each step we count the execution
path that results in the most possible queries, individually for each oracle index.
Minimal in the sense that any other query bound will be point-wise smaller than this query bound.
In general this count is not an actual possible result of simulating with `countingOracle`. -/
def minimalQueryBound : {α : Type} → OracleComp spec α → (ι → ℕ)
  | _, pure' _ _ => 0
  | _, queryBind' i _ _ oa => λ j ↦ (if j = i then 1 else 0) +
      (Finset.max' (Finset.univ.image <| λ u ↦ minimalQueryBound (oa u) j)
        (by simpa using Finset.univ_nonempty))

@[simp]
lemma minimalQueryBound_pure (x : α) :
    minimalQueryBound (pure x : OracleComp spec α) = 0 := rfl

@[simp]
lemma minimalQueryBound_query_bind (i : ι) (t : spec.domain i)
    (oa : spec.range i → OracleComp spec α) :
    minimalQueryBound (query i t >>= oa) = λ j ↦ (if j = i then 1 else 0) +
      (Finset.max' (Finset.univ.image <| λ u ↦ minimalQueryBound (oa u) j)
        (by simpa using Finset.univ_nonempty)) := rfl

lemma isQueryBound_minimalQueryBound (oa : OracleComp spec α) :
    IsQueryBound oa (minimalQueryBound oa) := by
  induction oa using OracleComp.inductionOn with
  | h_pure x => exact isQueryBound_pure x _
  | h_queryBind i t oa hoa =>
    · refine isQueryBound_bind (by simp) <| λ u _ ↦ isQueryBound_mono _ (hoa u)
        (λ j ↦ Finset.le_max' _ _ ?_)
      simp only [OracleComp.bind'_eq_bind, pure_bind, Finset.mem_image, Finset.mem_univ, true_and,
        exists_apply_eq_apply]

lemma minimalQueryBound_minimal (oa : OracleComp spec α) :
    Minimal (IsQueryBound oa) (minimalQueryBound oa) := by
  rw [minimal_iff]
  refine ⟨isQueryBound_minimalQueryBound oa, ?_⟩
  intro qc hqc h
  induction oa using OracleComp.inductionOn with
  | h_pure x => {
    simp at h
    simp [h]
  }
  | h_queryBind i t oa hoa => {
    simp at hqc h
    sorry
  }

-- lemma le_minimalQueryBound_of_isQueryBound {oa : OracleComp spec α} (qc : ι → ℕ)
--     (hqc : IsQueryBound oa qc) : minimalQueryBound oa ≤ qc := by
--   induction oa using OracleComp.inductionOn with
--   | h_pure x => {
--     exact zero_le _
--   }
--   | h_queryBind i t oa hoa => {
--     simp only [minimalQueryBound]
--     intro j
--     by_cases hj : j = i
--     · induction hj
--       simp only [↓reduceIte, OracleComp.bind'_eq_bind, pure_bind]
--       sorry
--     · simp [hj]
--       sorry
--   }

lemma exists_isQueryBound (oa : OracleComp spec α) : ∃ qc, IsQueryBound oa qc :=
  ⟨minimalQueryBound oa, isQueryBound_minimalQueryBound oa⟩

-- lemma exists_minimal_isQueryBound (oa : OracleComp spec α) :
--     ∃ qc, IsQueryBound oa qc ∧ (∀ qc', IsQueryBound oa qc' → qc ≤ qc') := by
--   refine ⟨minimalQueryBound oa, isQueryBound_minimalQueryBound oa,
--     le_minimalQueryBound_of_isQueryBound⟩

end minimalQueryBound

lemma isQueryBound_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) (qb : ι → ℕ) :
    IsQueryBound (oa >>= ob) qb ↔ ∃ (qb₁ : ι → ℕ) (qb₂ : α → ι → ℕ),
      IsQueryBound oa qb₁ ∧ (∀ u, IsQueryBound (ob u) (qb₂ u)) ∧ (∀ u, qb₁ + qb₂ u ≤ qb) := by
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · sorry
  · obtain ⟨qb₁, qb₂, hqb₁, hqb₂, h⟩ := h
    have hα : DecidableEq α := Classical.decEq α
    let qb₂' : ι → ℕ := λ i ↦ Finset.max' (oa.finSupport.image λ x ↦ qb₂ x i) (by simp)
    refine isQueryBound_mono (qb₁ + qb₂') ?_ ?_
    · refine isQueryBound_bind hqb₁ ?_
      intro x hx
      specialize hqb₂ x
      refine isQueryBound_mono (qb₂ x) hqb₂ ?_
      intro i
      refine Finset.le_max' _ _ ?_
      simp only [Finset.mem_image]
      refine ⟨x, ?_, rfl⟩
      refine mem_finSupport_of_mem_support _ hx
    · intro i
      refine Nat.add_le_of_le_sub' ?_ ?_
      · specialize h oa.defaultResult i
        refine le_trans ?_ h
        refine le_self_add
      · simp only [Finset.max'_le_iff, Finset.mem_image, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, qb₂']
        intro x hx
        specialize h x i
        rw [Nat.le_sub_iff_add_le']
        · exact h
        · refine le_trans le_self_add h

-- lemma isQueryBound_query_bind_iff (i : ι) (t : spec.domain i)
--     (oa : spec.range i → OracleComp spec α) (qc : ι → ℕ) :
--     IsQueryBound (query i t >>= oa) qc ↔ qc i ≠ 0 ∧
--       ∀ u, IsQueryBound (oa u) (Function.update qc i (qc i - 1)) := by
--   refine ⟨λ h ↦ ⟨?_, ?_⟩, λ h ↦ ?_⟩
--   · specialize h (minimalQueryBound (query i t >>= oa))
--     sorry
--   · sorry
--   · refine isQueryBound_mono (isQueryBound_bind (update_isQueryBound_query i t) h.2) ?_
--     intro j
--     by_cases hj : j = i
--     · simp only [hj, Pi.add_apply, Function.update_same]
--       rw [Nat.add_sub_of_le]
--       rw [Nat.one_le_iff_ne_zero]
--       exact h.1
--     · simp [hj]

@[simp]
lemma isQueryBound_map_iff (oa : OracleComp spec α) (f : α → β) (qb : ι → ℕ) :
    IsQueryBound (f <$> oa) qb ↔ IsQueryBound oa qb := by
  simp [isQueryBound_def]

-- isQueryBound_seq_iff

section simulate

variable {ι' : Type} {spec' : OracleSpec ι} {σ : Type}

-- /-- If we have a query bound on a computation, and a query bound on a `SimOracle` implementation,
-- then their product is a query bound on the -/
-- lemma isQueryBound_simulate (oa : OracleComp spec α) (so : spec →[σ]ₛₒ spec') (s : σ)
--     {qb qbs : ι → ℕ} (hqb : IsQueryBound oa qb) (hqbs : ∀ i t s, IsQueryBound (so i t s) qbs) :
--     IsQueryBound (simulate so s oa) (qb * qbs) := by
--   induction oa using OracleComp.inductionOn with
--   | h_pure x => exact isQueryBound_pure (x, s) (qb * qbs)
--   | h_queryBind i t oa hoa => {
--       rw [simulate_query_bind]
--       sorry
--   }

end simulate


-- @[simp]
-- lemma zero_isQueryBound_iff (oa : OracleComp spec α) :
--     IsQueryBound oa 0 ↔ isPure oa := by
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

/-- If `oa` is an computation indexed by a security parameter, then `PolyQueries oa`
means that for each oracle index there is a polynomial function `qb` of the security parameter,
such that the number of queries to that oracle is bounded by the corresponding polynomial. -/
structure PolyQueries {ι : Type} [DecidableEq ι] {spec : ℕ → OracleSpec ι}
  {α β : ℕ → Type} (oa : (n : ℕ) → α n → OracleComp (spec n) (β n)) where
  /-- `qb i` is a polynomial bound on the queries made to oracle `i`. -/
  qb : ι → Polynomial ℕ
  /-- The bound is actually a bound on the number of queries made. -/
  qb_isQueryBound (n : ℕ) (x : α n) :
    IsQueryBound (oa n x) (λ i ↦ (qb i).eval n)

end PolyQueries

end OracleComp
