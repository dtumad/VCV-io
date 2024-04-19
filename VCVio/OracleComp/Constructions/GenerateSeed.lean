/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.QueryTracking.CountingOracle
import VCVio.OracleComp.SimSemantics.QueryTracking.SeededOracle
import VCVio.OracleComp.DistSemantics.ActiveOracles
import VCVio.OracleComp.Constructions.Replicate
import VCVio.OracleComp.Constructions.UniformSelect

/-!
# Counting Queries Made by a Computation

This file defines a simulation oracle `countingOracle spec` for counting the number of queries made
while running the computation. The count is represented by a type `queryCount spec`,
which

-/

open OracleSpec ENNReal BigOperators

namespace OracleComp

variable {spec : OracleSpec} [∀ i, SelectableType (spec.range i)]


variable [∀ j, SelectableType (spec.range j)]

def generateSeedAux (qc : spec.ι → ℕ) : List spec.ι → QuerySeed spec →
    OracleComp unifSpec (QuerySeed spec)
  | [], seed => return seed
  | j :: js, seed => do
      let xs ← replicate ($ᵗ (spec.range j)) (qc j)
      let seed' := seed.addValues xs.toList
      generateSeedAux qc js seed'

def generateSeed (qc : spec.ι → ℕ) (activeOracles : List spec.ι) :
    OracleComp unifSpec (QuerySeed spec) :=
  generateSeedAux qc activeOracles ∅

end OracleComp
