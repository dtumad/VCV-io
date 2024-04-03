/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.QueryTracking.CountingOracle
import VCVio.OracleComp.DistSemantics.ActiveOracles

/-!
# Counting Queries Made by a Computation

This file defines a simulation oracle `countingOracle spec` for counting the number of queries made
while running the computation. The count is represented by a type `queryCount spec`,
which

-/

open OracleSpec

namespace OracleComp

-- structure QueryBound (oa : OracleComp spec α) where
--   count : QueryCount spec


-- structure

def IsQueryBound (oa : OracleComp spec α) (qb : QueryCount spec) : Prop :=
  ∀ count ∈ (Prod.snd <$> simulate countingOracle oa 0).support,
    ∀ i : spec.ι, count i ≤ qb i


end OracleComp
