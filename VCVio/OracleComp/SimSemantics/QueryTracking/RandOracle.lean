/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.QueryTracking.CachingOracle
import VCVio.OracleComp.SimSemantics.Constructions
import VCVio.OracleComp.Constructions.UniformSelect

/-!
# Random Oracles

This file defines a simulation oracle `randOracle` that uniformly responds to fresh queries,
but caches previous queries for future calls.

Implemented as a composition of caching and uniform oracles,
with the state of the uniform oracle masked away.
-/

open OracleSpec OracleComp

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} [∀ i, SelectableType (spec.range i)]
  {α β γ : Type} [spec.DecidableEq]

/-- Random oracles as a composition of a uniform oracle with a caching oracle.
NOTE: we could take the result of `apply_eq` as the maindefinition and give this one as a lemma. -/
def randOracle {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} [spec.DecidableEq]
    [∀ i, SelectableType (spec.range i)] : SimOracle spec unifSpec (QueryCache spec) :=
  (unifOracle ∘ₛₒ cachingOracle).maskState (Equiv.prodPUnit (QueryCache spec))

namespace randOracle

-- /-- Executing a random oracle is the same as lookuping up the value and choosing a uniformly
-- random new value if it doesn't already exist. -/
-- @[simp]
-- lemma apply_eq (q : OracleQuery spec α) (cache : QueryCache spec) :
--     randOracle.impl q cache = cache.lookup_or_else i t ($ᵗ spec.range i) := by
--   simp only [randOracle, SimOracle.maskState_apply, Equiv.prodPUnit_symm_apply,
--     SimOracle.compose_apply, cachingOracle.apply_eq, QueryCache.lookup_or_else, Functor.map_map,
--     Function.comp, Prod.map_apply, id_eq, Equiv.prodPUnit_apply, Prod.mk.eta]
--   sorry
  -- cases cache i t

  -- · simp [map_eq_bind_pure_comp]
  -- · simp

-- /-- Simulation with a random oracle looks like choosing a random function and answering queries
-- with that. TODO: there's some tricky things in the induction step here. -/
-- lemma evalDist_simulate'_eq_uniformSelect_fun_bind
--     [Inhabited γ] [Fintype γ] [Fintype β] [DecidableEq β]
--     [DecidableEq γ] [SelectableType γ]
--     [SelectableType (β → γ)]
--     (oa : OracleComp (β →ₒ γ) α) :
--     [simulate' randOracle ∅ oa] = [do
--       let f ←$ᵗ (β → γ)
--       simulate' (λ () t () ↦ return (f t, ())) () oa] := by
--   sorry

end randOracle
