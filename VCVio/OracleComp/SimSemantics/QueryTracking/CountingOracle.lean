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

open OracleComp OracleSpec Function

/-- Oracle for counting the number of queries made by a computation. The count is stored as a
function from oracle indices to counts, to give finer grained information about the count. -/
def countingOracle {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} :
    spec →[ι → ℕ]ₛₒ spec :=
  λ i t qc ↦ (·, update qc i (qc i + 1)) <$> query i t

namespace countingOracle

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} {α β γ : Type}

@[simp]
lemma apply_eq (i : ι) (t : spec.domain i) :
    countingOracle i t = λ qc ↦ (·, update qc i (qc i + 1)) <$> query i t := rfl

/-- We can always reduce the initial state of simulation with a counting oracle to start with a
count of zero, and add the initial count back on at the end. -/
lemma support_simulate (oa : OracleComp spec α) (qc : ι → ℕ) :
    (simulate countingOracle qc oa).support =
      Prod.map id (qc + ·) '' (simulate countingOracle 0 oa).support := by
  revert qc
  induction oa using OracleComp.inductionOn with
  | h_pure a => simp
  | h_queryBind i t oa hoa =>
      refine λ qc ↦ ?_
      simp only [simulate_bind, simulate_query, apply_eq, support_bind, support_map, support_query,
        Set.image_univ, Set.mem_range, Set.iUnion_exists, Set.iUnion_iUnion_eq', Prod.map_apply,
        id_eq, Pi.zero_apply, zero_add, Set.image_iUnion]
      refine Set.iUnion_congr (λ u ↦ ?_)
      simp only [hoa u (update qc i (qc i + 1)), hoa u (update 0 i 1),
        ← Set.image_comp, Function.comp, Prod.map_apply, id_eq, ← add_assoc]
      refine Set.image_congr' (λ z ↦ Prod.eq_iff_fst_eq_snd_eq.2 ⟨rfl, funext (λ j ↦ ?_)⟩)
      by_cases hij : j = i <;> simp [hij]

/-- Reduce membership in the support of simulation with counting to membership in simulation
starting with the count at `0`.
TODO: lemmas like this suggest maybe support shouldn't auto reduce? -/
lemma mem_support_simulate_iff_exists (oa : OracleComp spec α) (qc : ι → ℕ) (z : α × (ι → ℕ)) :
    z ∈ (simulate countingOracle qc oa).support ↔
      ∃ qc', (z.1, qc') ∈ (simulate countingOracle 0 oa).support ∧ qc + qc' = z.2 := by
  rw [support_simulate]
  simp only [Prod.map_apply, id_eq, Set.mem_image, Prod.eq_iff_fst_eq_snd_eq, Prod.exists]
  refine ⟨λ h ↦ let ⟨x, qc', h, hx, hqc'⟩ := h; ⟨qc', hx ▸ ⟨h, hqc'⟩⟩,
    λ h ↦ let ⟨qc', h, hqc'⟩ := h; ⟨z.1, qc', h, rfl, hqc'⟩⟩

lemma le_of_mem_support_simulate (oa : OracleComp spec α) (qc : ι → ℕ) (z : α × (ι → ℕ))
    (h : z ∈ (simulate countingOracle qc oa).support) : qc ≤ z.2 := by
  rw [mem_support_simulate_iff_exists] at h
  exact let ⟨qc', _, h⟩ := h; h ▸ le_self_add

end countingOracle
