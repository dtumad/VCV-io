/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.EvalDist
import ToMathlib.Control.WriterT

/-!
# Lemmas About the Distribution Semantics of `simulateQ`

This file collects various lemmas about the output distributions of `simulateQ`
-/


open OracleSpec Option ENNReal BigOperators

universe u v w

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type u} [hs : spec.FiniteRange]

/-- If `fst <$> so i (t, s)` has the same distribution as `query i t` for any state `s`,
Then `simulate' so` doesn't change the output distribution.
Stateless oracles are the most common example of this
TODO: move-/
lemma evalDist_simulate'_eq_evalDist {σ α : Type u}
    (so : QueryImpl spec (StateT σ (OracleComp spec)))
    (h : ∀ i t s, (evalDist ((so.impl (query i t)).run' s)) =
      OptionT.lift (PMF.uniformOfFintype (spec.range i)))
    (s : σ) (oa : OracleComp spec α) : evalDist (simulate' so s oa) = evalDist oa := by
  revert s
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind i t oa hoa => exact (λ s ↦ by
      simp only [StateT.run'_eq] at h
      simp only [simulate'_bind, simulate_query, evalDist_bind, Function.comp_def, hoa,
        evalDist_query, ← h i t s, evalDist_map, PMF.bind_map, hoa, bind_map_left])
  | failure => intro s; rw [simulate'_failure]

-- lemma probFailure_simulateQ_WriterT_eq_probFailure {ω : Type u} [Monoid ω]
--     (so : QueryImpl spec (WriterT ω (OracleComp spec)))
--     (h : ∀ {α}, ∀ q : OracleQuery spec α, [⊥ | (so.impl q).run] = 0) (oa : OracleComp spec α) :
--     [⊥ | (simulateQ so oa).run] = [⊥ | oa] := by
--   -- revert s
--   induction oa using OracleComp.inductionOn with
--   | pure x => simp
--   | failure => simp
--   | query_bind i t oa hq => {
--     simp [probFailure_bind_eq_tsum, h, hq]
--     intro s
--     rw [ENNReal.tsum_prod']
--     refine tsum_congr fun x => ?_
--     simp [ENNReal.tsum_mul_right]
--     congr 1

--     sorry
--   }

end OracleComp
