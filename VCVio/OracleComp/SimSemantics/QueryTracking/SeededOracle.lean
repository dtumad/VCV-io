/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Simulate

/-!
# Seeding Results of Queries

-/

open OracleComp OracleSpec BigOperators

variable {ι : Type} {spec : OracleSpec ι}

namespace OracleSpec

def QuerySeed (spec : OracleSpec ι) : Type :=
  (i : ι) → List (spec.range i)

namespace QuerySeed

-- instance : Coe (QuerySeed spec) (QueryCount spec) where
--   coe := λ qs i ↦ (qs i).length

-- def toCount (qs : QuerySeed spec) : QueryCount spec := λ i ↦ (qs i).length

instance : EmptyCollection (QuerySeed spec) := ⟨λ _ ↦ []⟩

def addValue [DecidableEq ι] (qs : QuerySeed spec) (i : ι) (u : spec.range i) : QuerySeed spec :=
  Function.update qs i (qs i ++ [u])

def addValues [DecidableEq ι] (qs : QuerySeed spec) {i : ι}
    (us : List (spec.range i)) : QuerySeed spec :=
  Function.update qs i (qs i ++ us)
--   -- λ j ↦ qs j ++ if h : j = i then h ▸ us else ∅

-- def takeAtIndex (qs : QuerySeed spec) {i : spec.ι}
--     (n : ℕ) : QuerySeed spec :=
--   λ j ↦ if j = i then (qs j).take n else qs j

-- def append (qs qs' : QuerySeed spec) : QuerySeed spec :=
--   λ i ↦ qs i ++ qs' i

end QuerySeed

end OracleSpec

def seededOracle [DecidableEq ι] : spec →[QuerySeed spec]ₛₒ spec :=
  λ i t seed ↦ match seed i with
    | u :: us => return (u, Function.update seed i us)
    | [] => (·, ∅) <$> query i t

namespace seededOracle

end seededOracle
