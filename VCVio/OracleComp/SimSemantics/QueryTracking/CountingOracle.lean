/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Simulate

/-!
# Counting Queries Made by a Computation

This file defines a simulation oracle `countingOracle` for counting the number of queries made
while running the computation. The count is represented by a function from oracle indices to
counts, allowing each oracle to be tracked individually.

Tracking individually is not necessary, but gives tighter security bounds in some cases.
It also allows for generating things like seed values for a computation more tightly.
-/

open OracleComp

-- namespace OracleSpec

-- @[inline, reducible]
-- def QueryCount (spec : OracleSpec) : Type := spec.ι → ℕ

-- variable {spec : OracleSpec}

-- def QueryCount.increment (qc : spec.QueryCount) (i : spec.ι) (n : ℕ) : spec.QueryCount :=
--   Function.update qc i (qc i + n)

-- def QueryCount.decrement (qc : spec.QueryCount) (i : spec.ι) (n : ℕ) : spec.QueryCount :=
--   Function.update qc i (qc i - n)

-- instance : Zero (QueryCount spec) := ⟨λ _ ↦ 0⟩

-- end OracleSpec

open OracleComp OracleSpec Function

def countingOracle {ι : Type} [DecidableEq ι]
    {spec : OracleSpec ι} : spec →[ι → ℕ]ₛₒ spec :=
  λ i t qc ↦ (·, update qc i (qc i + 1)) <$> query i t

namespace countingOracle

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} {α β γ : Type}

@[simp]
lemma apply_eq (i : ι) (t : spec.domain i) :
    countingOracle i t = λ qc ↦ (·, update qc i (qc i + 1)) <$> query i t := rfl

/-- Reduce membership in the support of simulation with counting to membership in simulation
starting with the count at `0`. -/
lemma mem_support_simulate_iff (oa : OracleComp spec α) (qc : ι → ℕ) (z : α × (ι → ℕ)) :
    z ∈ (simulate countingOracle qc oa).support ↔
      ∃ qc', (z.1, qc') ∈ (simulate countingOracle 0 oa).support ∧ qc + qc' = z.2 := by
  revert qc
  induction oa using OracleComp.inductionOn with
  | h_pure a => {
    simp [Prod.eq_iff_fst_eq_snd_eq, and_assoc, eq_comm]
  }
  | h_queryBind i t oa hoa => {
    simp
    intro qc
    refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
    · obtain ⟨u, hu⟩ := h
      rw [hoa] at hu
      obtain ⟨qc', hqc', hqc''⟩ := hu
      refine ⟨update qc' i (qc' i + 1), ⟨u, ?_⟩, ?_⟩
      · rw [hoa]
        simp
        refine ⟨qc', hqc', ?_⟩
        simp [funext_iff]
        intro j
        by_cases hij : j = i
        · induction hij
          simp [add_comm 1]
        · simp [Function.update_noteq hij]
      · simp [funext_iff, ← hqc'']
        intro j
        by_cases hij : j = i
        · induction hij
          simp [add_comm 1]
          ring_nf
        · simp [Function.update_noteq hij]
    · obtain ⟨qc', ⟨u, hu⟩, hqc'⟩ := h
      refine ⟨u, ?_⟩
      rw [hoa]
      rw [hoa] at hu
      simp at hu
      obtain ⟨qc'', hqc'', hu⟩ := hu
      refine ⟨qc'', hqc'', ?_⟩
      rw [← hqc', ← hu]
      simp [funext_iff]
      intro j
      by_cases hij : j = i
      · induction hij
        simp
        ring_nf
      · simp [Function.update_noteq hij]
  }

lemma support_simulate_mono (oa : OracleComp spec α) (qc : ι → ℕ) (z : α × (ι → ℕ))
    (h : z ∈ (simulate countingOracle qc oa).support) : qc ≤ z.2 := by
  -- rw [mem_support_]
  sorry

end countingOracle
