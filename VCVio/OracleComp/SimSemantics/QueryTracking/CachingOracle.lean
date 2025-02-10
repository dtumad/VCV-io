/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Simulate

/-!
# Caching Queries Made by a Computation

This file defines a simulation oracle `cachingOracle` for caching queries to the oracles,
querying fresh values if needed. This is mainly used for constructing random oracles that will
further respond uniformly to queries.
-/

open OracleComp OracleSpec

universe u v w

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι} {α β : Type u}

namespace OracleSpec

/-- Type to represent a cache of queries to oracles in `spec`.
Defined to be a function from (indexed) inputs to an optional output. -/
def QueryCache (spec : OracleSpec ι) : Type u :=
  (i : ι) → spec.domain i → Option (spec.range i)

namespace QueryCache

instance : EmptyCollection (QueryCache spec) := ⟨λ _ _ ↦ none⟩

section cacheQuery

variable [spec.DecidableEq] (cache : QueryCache spec)

/-- Add a index + input pair to the cache by updating the function -/
def cacheQuery (i : ι) (t : spec.domain i) (u : spec.range i) :
    QueryCache spec := Function.update cache i (Function.update (cache i) t u)

lemma cacheQuery_eq_ite_ite (i : ι) (t : spec.domain i) (u : spec.range i) :
    cache.cacheQuery i t u = λ j t' ↦
      if h : j = i then (if h ▸ t' = t then some (h ▸ u) else cache j t') else cache j t' := by
  refine funext (λ j ↦ funext (λ t' ↦ ?_))
  by_cases h : j = i
  · induction h
    by_cases ht : t' = t
    · simp [ht, cacheQuery]
    · simp [ht, cacheQuery]
  · simp [h, cacheQuery]

end cacheQuery

def queryFresh [spec.DecidableEq] (i : ι) (t : spec.domain i) :
    StateT spec.QueryCache (OracleComp spec) (spec.range i) := do
  let u ← query i t
  modifyGet fun cache => (u, cache.cacheQuery i t u)

end QueryCache

end OracleSpec

/-- Oracle for caching queries to the oracles in `spec`, querying fresh values if needed. -/
def cachingOracle [spec.DecidableEq] :
    QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) where
  impl | query i t => do match (← get) i t with
    | Option.some u => return u
    | Option.none => QueryCache.queryFresh i t

namespace cachingOracle

variable [spec.DecidableEq]

@[simp]
lemma apply_eq (q : OracleQuery spec α) : cachingOracle.impl q =
    match q with | query i t => (do match (← get) i t with
      | Option.some u => return u
      | Option.none => QueryCache.queryFresh i t) :=
  rfl

end cachingOracle
