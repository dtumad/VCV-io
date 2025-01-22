/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Simulate

/-!
# Simulation Oracles for Tracking

This file defines a typeclass `SimOracle.IsTracking so` when `so` is only tracking some information
in the state (e.g. a log of queries), without changing the actual query responses.
-/

open OracleSpec OracleComp

universe u v w

namespace SimOracle

variable {ι : Type u} {spec : OracleSpec ι} {α σ : Type w} (so : SimOracle spec spec σ)

lemma run'_simulateT_eq_self (h : ∀ α (q : OracleQuery spec α) s, (so.impl q).run' s = q)
    (oa : OracleComp spec α) (s : σ) : (simulateT so oa).run' s = oa := by
  revert s
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | failure => simp
  | query_bind i t oa hoa =>
      intro s
      simp [hoa, -StateT.run'_eq]
      simp at hoa
      simp [hoa]
      rw [← h (spec.range i) (query i t) s]
      simp only [bind_map_left, StateT.run']
      rfl

lemma simulate'_eq_self (h : ∀ α (q : OracleQuery spec α) s, (so.impl q).run' s = q)
    (s : σ) (oa : OracleComp spec α) : simulate' so s oa = oa :=
  run'_simulateT_eq_self so h oa s

/-- Typeclass for simulation oracles that only perform some kind of tracking (e.g. logging).
In this case `StateT.run'` will reduce a simulated computation to itself. -/
class IsTracking (so : spec →[σ]ₛₒ spec) where
    state_indep : ∀ {α} (q : OracleQuery spec α) s, (so.impl q).run' s = q

namespace IsTracking

@[simp]
lemma run'_simulateT_eq_self (so : SimOracle spec spec σ) [IsTracking so]
    (oa : OracleComp spec α) (s : σ) : (simulateT so oa).run' s = oa :=
  simulate'_eq_self so (λ _ (query i _) _ ↦ IsTracking.state_indep _ _) s oa

@[simp]
lemma fst_map_run_simulateT_eq_slef (so : SimOracle spec spec σ) [IsTracking so]
    (oa : OracleComp spec α) (s : σ) : Prod.fst <$> (simulateT so oa).run s = oa :=
  IsTracking.run'_simulateT_eq_self so oa s

@[simp]
lemma simulate'_eq_self (so : spec →[σ]ₛₒ spec) [IsTracking so]
    (s : σ) (oa : OracleComp spec α) : simulate' so s oa = oa :=
  IsTracking.run'_simulateT_eq_self so oa s

lemma mem_support_of_mem_support_simulate' {so : spec →[σ]ₛₒ spec} [IsTracking so]
    {s : σ} {oa : OracleComp spec α} {x : α}
    (h : x ∈ (simulate' so s oa).support) : x ∈ oa.support := by
  rwa [simulate'_eq_self] at h

end IsTracking

end SimOracle
