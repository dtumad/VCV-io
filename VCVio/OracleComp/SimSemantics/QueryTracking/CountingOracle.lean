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

section support

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
      by_cases hij : j = i <;> simp [hij, add_assoc]

/-- Reduce membership in the support of simulation with counting to membership in simulation
starting with the count at `0`.
TODO: lemmas like this suggest maybe support shouldn't auto reduce on the computation type? -/
lemma mem_support_simulate_iff (oa : OracleComp spec α) (qc : ι → ℕ) (z : α × (ι → ℕ)) :
    z ∈ (simulate countingOracle qc oa).support ↔
      ∃ qc', (z.1, qc') ∈ (simulate countingOracle 0 oa).support ∧ qc + qc' = z.2 := by
  rw [support_simulate]
  simp only [Prod.map_apply, id_eq, Set.mem_image, Prod.eq_iff_fst_eq_snd_eq, Prod.exists]
  exact ⟨λ h ↦ let ⟨x, qc', h, hx, hqc'⟩ := h; ⟨qc', hx ▸ ⟨h, hqc'⟩⟩,
    λ h ↦ let ⟨qc', h, hqc'⟩ := h; ⟨z.1, qc', h, rfl, hqc'⟩⟩

lemma mem_support_simulate_iff_of_le (oa : OracleComp spec α) (qc : ι → ℕ) (z : α × (ι → ℕ))
    (hz : qc ≤ z.2) : z ∈ (simulate countingOracle qc oa).support ↔
      (z.1, z.2 - qc) ∈ (simulate countingOracle 0 oa).support := by
  rw [mem_support_simulate_iff oa 0]
  simp only [mem_support_simulate_iff oa qc z, zero_add, exists_eq_right]
  refine ⟨λ ⟨qc', h, hqc'⟩ ↦ ?_, λ h ↦ ?_⟩
  · convert h
    refine funext (λ x ↦ ?_)
    rw [Pi.sub_apply, Nat.sub_eq_iff_eq_add' (hz x)]
    exact symm (congr_fun hqc' x)
  · refine ⟨z.2 - qc, h, ?_⟩
    refine funext (λ x ↦ ?_)
    refine Nat.add_sub_cancel' (hz x)

lemma mem_support_snd_map_simulate_iff (oa : OracleComp spec α) (qc qc' : ι → ℕ) :
    qc' ∈ (Prod.snd <$> simulate countingOracle qc oa).support ↔
      ∃ qc'', ∃ x, (x, qc'') ∈ (simulate countingOracle 0 oa).support ∧ qc + qc'' = qc' := by
  simp only [support_map, Set.mem_image, Prod.exists, exists_eq_right]
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · obtain ⟨x, hx⟩ := h
    rw [mem_support_simulate_iff] at hx
    obtain ⟨qc'', h, hqc''⟩ := hx
    refine ⟨qc'', x, h, hqc''⟩
  · obtain ⟨qc'', x, h, hqc''⟩ := h
    refine ⟨x, ?_⟩
    rw [mem_support_simulate_iff]
    refine ⟨qc'', h, hqc''⟩

lemma mem_support_snd_map_simulate_iff_of_le (oa : OracleComp spec α) {qc qc' : ι → ℕ}
    (hqc : qc ≤ qc') : qc' ∈ (Prod.snd <$> simulate countingOracle qc oa).support ↔
      qc' - qc ∈ (Prod.snd <$> simulate countingOracle 0 oa).support := by
  simp only [mem_support_snd_map_simulate_iff, zero_add]
  refine exists_congr (λ qc'' ↦ exists_congr (λ x ↦ ?_))
  refine and_congr_right' ?_
  refine ⟨λ h ↦ funext (λ x ↦ ?_), λ h ↦ funext (λ x ↦ ?_)⟩
  · rw [← h]
    refine symm ?_
    refine Nat.add_sub_cancel_left _ _
  · rw [h]
    refine Nat.add_sub_cancel' (hqc x)

lemma le_of_mem_support_simulate {oa : OracleComp spec α} {qc qc' : ι → ℕ} {x : α}
    (h : (x, qc') ∈ (simulate countingOracle qc oa).support) : qc ≤ qc' := by
  rw [mem_support_simulate_iff] at h
  obtain ⟨qc'', _, h⟩ := h
  exact le_of_le_of_eq le_self_add h

lemma mem_support_simulate_pure_iff (x : α) (qc : ι → ℕ) (z : α × (ι → ℕ)) :
    z ∈ (simulate countingOracle qc (pure x : OracleComp spec α)).support ↔ z = (x, qc) := by
  simp only [simulate_pure, support_pure, Set.mem_singleton_iff]

lemma mem_support_simulate_queryBind_iff (i : ι) (t : spec.domain i)
    (oa : spec.range i → OracleComp spec α) (qc : ι → ℕ) (z : α × (ι → ℕ)) :
    z ∈ (simulate countingOracle qc (query i t >>= oa)).support ↔ z.2 i ≠ 0 ∧ ∃ u,
      (z.1, Function.update z.2 i (z.2 i - 1)) ∈ (simulate countingOracle qc (oa u)).support := by
  rw [mem_support_simulate_iff, simulate_query_bind]
  rw [support_bind]
  simp only [apply_eq, Pi.zero_apply, zero_add, support_map, support_query, Set.image_univ,
    Set.mem_range, Set.iUnion_exists, Set.iUnion_iUnion_eq', Set.mem_iUnion]
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · obtain ⟨qc', ⟨⟨u, hu⟩, hqc⟩⟩ := h
    refine ⟨?_, ?_⟩
    · have := le_of_mem_support_simulate hu i
      rw [← hqc, Pi.add_apply]
      rw [← Nat.pos_iff_ne_zero]
      refine Nat.add_pos_right _ ?_
      refine lt_of_lt_of_le ?_ this
      simp
    · refine ⟨u, ?_⟩
      simp [← hqc]
      rw [mem_support_simulate_iff_of_le]
      · simp

        rw [mem_support_simulate_iff_of_le] at hu
        · simp at hu
          convert hu using 2
          refine funext (λ j ↦ ?_)
          by_cases hj : j = i
          · simp [hj]

            sorry
          · simp [hj]
        · intro j

          by_cases hj : j = i
          · induction hj
            simp only [update_same]
            have := le_of_mem_support_simulate hu j
            refine le_trans ?_ this
            simp
          · simp [hj]
      · intro j
        by_cases hj : j = i
        · induction hj
          simp

          sorry
        · simp [hj]
  · obtain ⟨hz, ⟨u, hu⟩⟩ := h

    sorry


end support

end countingOracle
