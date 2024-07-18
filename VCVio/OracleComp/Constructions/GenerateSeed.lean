/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.QueryTracking.SeededOracle
import VCVio.OracleComp.Constructions.Replicate
import VCVio.OracleComp.Constructions.UniformSelect

/-!
# Counting Queries Made by a Computation

This file defines a simulation oracle `countingOracle spec` for counting the number of queries made
while running the computation. The count is represented by a type `queryCount spec`,
which

-/

open Mathlib OracleSpec ENNReal BigOperators

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} [∀ i, SelectableType (spec.range i)]

def generateSeedAux [DecidableEq ι] (qc : ι → ℕ) : List ι → QuerySeed spec →
    OracleComp unifSpec (QuerySeed spec)
  | [], seed => return seed
  | j :: js, seed => do
      let xs ← Vector.toList <$> replicate ($ᵗ (spec.range j)) (qc j)
      generateSeedAux qc js (Function.update seed j (seed j ++ xs))

def generateSeed [DecidableEq ι] (qc : ι → ℕ) (activeOracles : List ι) :
    OracleComp unifSpec (QuerySeed spec) :=
  generateSeedAux qc activeOracles ∅

end OracleComp
