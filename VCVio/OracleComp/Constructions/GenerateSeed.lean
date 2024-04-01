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

def generateSeedAux (oa : OracleComp spec α) (count : QueryCount spec) :
    List spec.ι → OracleComp unifSpec (QuerySeed spec)
  | (j :: js) => do
    let xs ← replicate ($ᵗ (spec.range j)) (count j)
    let seed ← generateSeedAux oa count js
    return Function.update seed j xs.toList
  | [] => return ∅

noncomputable def generateSeed (oa : OracleComp spec α)
    (count : QueryCount spec) : OracleComp unifSpec (QuerySeed spec) :=
  generateSeedAux oa count oa.activeOracles.toList

end OracleComp
