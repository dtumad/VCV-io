/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.QueryTracking.CachingOracle

/-!
# Random Oracles

This file defines a simulation oracle `randOracle` that uniformly responds to fresh queries,
but caches previous queries for future calls.

Implemented as a composition of caching and uniform oracles,
with the state of the uniform oracle masked away.
-/

open OracleSpec OracleComp

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} [∀ i, SelectableType (spec.range i)]

/-- Random oracles as a composition of a uniform oracle with a caching oracle. -/
def randOracle {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
    [∀ i, SelectableType (spec.range i)] : spec →[QueryCache spec]ₛₒ unifSpec :=
  (unifOracle ∘ₛₒ cachingOracle).maskState (Equiv.prodPUnit (QueryCache spec))

namespace randOracle

/-- Executing a random oracle is the same as lookuping up the value and choosing a uniformly
random new value if it doesn't already exist. -/
@[simp]
lemma apply_eq (i : ι) (t : spec.domain i) (cache : QueryCache spec) :
    randOracle i t cache = cache.lookup_or_else i t ($ᵗ spec.range i) := by
  simp [randOracle, Functor.map_map, Function.comp, QueryCache.lookup_or_else]
  cases cache i t
  · simp [map_eq_bind_pure_comp]
  · simp

end randOracle
