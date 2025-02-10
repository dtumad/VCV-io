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

universe u v w

/-- Random oracles as a composition of a uniform oracle with a caching oracle.
NOTE: composition isn't quite general enough for `(unifOracle ∘ₛ cachingOracle)` to work. -/
def randOracle {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} [spec.DecidableEq]
    [∀ i, SelectableType (spec.range i)] :
    QueryImpl spec (StateT spec.QueryCache (OracleComp unifSpec)) where
  impl | query i t => do match (← get) i t with
    | Option.some u => return u
    | Option.none => do
      let u ←$ᵗ spec.range i
      modifyGet fun cache => (u, cache.cacheQuery i t u)

namespace randOracle

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} [spec.DecidableEq]
    [∀ i, SelectableType (spec.range i)] {α β γ : Type}

@[simp] -- TODO: think about simp paths with `mk`/``run`
lemma simulateQ_eq' (oa : OracleComp spec α) : simulateQ randOracle oa =
    StateT.mk (simulateQ unifOracle ∘ (simulateQ cachingOracle oa).run) :=
  sorry

/-- Simulation with `randOracle` is just simulation with `cachingOracle` then `unifOracle`. -/
lemma simulateQ_eq (oa : OracleComp spec α) : simulateQ randOracle oa =
    simulateQ unifOracle ∘ simulateQ cachingOracle oa :=
  sorry

end randOracle
