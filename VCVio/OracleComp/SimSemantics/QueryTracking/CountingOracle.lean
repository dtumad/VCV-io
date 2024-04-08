/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Simulate

/-!
# Counting Queries Made by a Computation

This file defines a simulation oracle `countingOracle spec` for counting the number of queries made
while running the computation. The count is represented by a type `queryCount spec`,
which

-/

open OracleComp

namespace OracleSpec

def QueryCount (spec : OracleSpec) : Type := spec.ι → ℕ

variable {spec : OracleSpec}

def QueryCount.increment (qc : spec.QueryCount) (i : spec.ι) (n : ℕ) : spec.QueryCount :=
  Function.update qc i (qc i + n)

def QueryCount.decrement (qc : spec.QueryCount) (i : spec.ι) (n : ℕ) : spec.QueryCount :=
  Function.update qc i (qc i - n)

instance : Zero (QueryCount spec) := ⟨λ _ ↦ 0⟩

end OracleSpec

open OracleComp OracleSpec

def countingOracle {spec : OracleSpec} :
    spec →[QueryCount spec]ₛₒ spec :=
  λ i t qc ↦ (·, qc.increment i 1) <$> query i t

-- def countingOracle {spec : OracleSpec} :
--   spec →[List spec.ι]ₛₒ spec :=
-- λ i ⟨t, qc⟩ ↦ (·, i :: qc) <$> query i t

namespace countingOracle

end countingOracle
