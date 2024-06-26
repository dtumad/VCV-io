/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Constructions
import VCVio.OracleComp.Constructions.UniformSelect

/-!
# Caching Queries Made by a Computation

-/

open OracleComp OracleSpec

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} {α β : Type}

namespace OracleSpec

/-- Type to represent a cache of queries to oracles in `spec`.
Defined to be a function from (indexed) inputs to an optional output. -/
def QueryCache (spec : OracleSpec ι) : Type :=
  (i : ι) → spec.domain i → Option (spec.range i)

namespace QueryCache

variable (cache : QueryCache spec)

instance : EmptyCollection (QueryCache spec) := ⟨λ _ _ ↦ none⟩

section cacheQuery

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

section lookup_or_query

variable {ι' : Type} {spec' : OracleSpec ι'}

/-- Lookup a value in the cache, querying a fresh value if no value is cached.
Returns both the value and updated cache. -/
def lookup_or_else (cache : QueryCache spec) (i : ι) (t : spec.domain i)
    (oq : OracleComp spec' (spec.range i)) :
    OracleComp spec' (spec.range i × QueryCache spec) :=
  match cache i t with
  | Option.some u => return (u, cache)
  | Option.none => do let u ← oq; return (u, cache.cacheQuery i t u)

@[simp]
lemma lookup_or_else_empty (i : ι) (t : spec.domain i) (oq : OracleComp spec' (spec.range i)) :
    lookup_or_else ∅ i t oq = do let u ← oq; return (u, cacheQuery ∅ i t u) := rfl

end lookup_or_query

end QueryCache

end OracleSpec

/-- Oracle for caching queries to the oracles in `spec`, querying fresh values if needed. -/
def cachingOracle {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} :
    spec →[QueryCache spec]ₛₒ spec :=
  λ i t cache ↦ cache.lookup_or_else i t (query i t)

namespace cachingOracle

@[simp]
lemma apply_eq (i : ι) (t : spec.domain i) (cache : QueryCache spec) :
    cachingOracle i t cache = cache.lookup_or_else i t (query i t) := rfl

end cachingOracle
