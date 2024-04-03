/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Simulate

/-!
# Caching Queries Made by a Computation

-/

namespace OracleSpec

def QueryCache (spec : OracleSpec) : Type :=
  (i : spec.ι) → spec.domain i → Option (spec.range i)

def QueryCache.cacheQuery {spec : OracleSpec} (cache : QueryCache spec) {i : spec.ι}
    (t : spec.domain i) (u : spec.range i) : QueryCache spec :=
  Function.update cache i (Function.update (cache i) t u)

end OracleSpec

open OracleComp OracleSpec

def cachingOracle {spec : OracleSpec} :
    spec →[QueryCache spec]ₛₒ spec :=
  λ i ⟨t, cache⟩ ↦ match cache i t with
    | Option.some u => return (u, cache)
    | Option.none => do
        let u ← query i t
        return (u, cache.cacheQuery t u)
