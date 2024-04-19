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

open Option

namespace OracleSpec

def QueryCache (spec : OracleSpec) : Type :=
  (i : spec.ι) → spec.domain i → Option (spec.range i)

def QueryCache.cacheQuery {spec : OracleSpec} (cache : QueryCache spec) {i : spec.ι}
    (t : spec.domain i) (u : spec.range i) : QueryCache spec :=
  Function.update cache i (Function.update (cache i) t u)

instance : EmptyCollection (QueryCache spec) := ⟨λ _ _ ↦ none⟩

end OracleSpec

open OracleComp OracleSpec

def cachingOracle {spec : OracleSpec} :
    spec →[QueryCache spec]ₛₒ spec :=
  λ i t cache ↦ match cache i t with
    | Option.some u => return (u, cache)
    | Option.none => do
        let u ← query i t
        return (u, cache.cacheQuery t u)

namespace cachingOracle

-- ort

end cachingOracle

def randOracle {spec : OracleSpec}
    [∀ i, SelectableType (spec.range i)] :
    spec →[QueryCache spec]ₛₒ unifSpec :=
  (unifOracle ∘ₛₒ cachingOracle).maskState
    (Equiv.prodPUnit (QueryCache spec))

namespace randOracle

-- port

end randOracle
