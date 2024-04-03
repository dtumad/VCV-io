/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Simulate

/-!
# Seeding Results of Queries

-/

variable {spec : OracleSpec}

namespace OracleSpec

def QuerySeed (spec : OracleSpec) : Type :=
  (i : spec.ι) → List (spec.range i)

instance : EmptyCollection (QuerySeed spec) := ⟨λ _ ↦ []⟩

end OracleSpec

open OracleComp OracleSpec

def seededOracle : spec →[QuerySeed spec]ₛₒ spec :=
  λ i ⟨t, seed⟩ ↦ match seed i with
    | u :: us => return (u, Function.update seed i us)
    | [] => (·, seed) <$> query i t
