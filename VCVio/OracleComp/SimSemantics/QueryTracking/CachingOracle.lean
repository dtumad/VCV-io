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

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

namespace OracleSpec

def QueryCache {ι : Type} (spec : OracleSpec ι) : Type :=
  (i : ι) → spec.domain i → Option (spec.range i)

instance : EmptyCollection (QueryCache spec) := ⟨λ _ _ ↦ none⟩

def QueryCache.cacheQuery {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
    (cache : QueryCache spec) (i : ι)
    (t : spec.domain i) (u : spec.range i) : QueryCache spec :=
  Function.update cache i (Function.update (cache i) t u)

instance : EmptyCollection (QueryCache spec) := ⟨λ _ _ ↦ none⟩

end OracleSpec

open OracleComp OracleSpec

def cachingOracle {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} :
    spec →[QueryCache spec]ₛₒ spec :=
  λ i t cache ↦ match cache i t with
    | Option.some u => return (u, cache)
    | Option.none => do let u ← query i t; return (u, cache.cacheQuery i t u)

namespace cachingOracle

-- port

end cachingOracle

def randOracle {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
    [∀ i, SelectableType (spec.range i)] :
    spec →[QueryCache spec]ₛₒ unifSpec :=
  (unifOracle ∘ₛₒ cachingOracle).maskState (Equiv.prodPUnit (QueryCache spec))

namespace randOracle

-- port

end randOracle
