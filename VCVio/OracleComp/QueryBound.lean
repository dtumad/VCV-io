/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.QueryTracking.CountingOracle

/-!
# Bounding Queries Made by a Computation

This file defines a predicate `IsQueryBound oa qb` to say that a computation with oracles `spec`
never makes a larger number of queries than is given by a bound `qb : spec.ι → ℕ`.
This is useful for showing that some simulated computation is polynomial time,
and in things like seeding query values for a computation.
-/

open OracleSpec

namespace OracleComp

variable {spec : OracleSpec} {α : Type}

/-- Bound on the number of queries made by a computation, given by a map from oracles to counts. -/
def IsQueryBound (oa : OracleComp spec α) (qb : spec.ι → ℕ) : Prop :=
  ∀ count ∈ (Prod.snd <$> simulate countingOracle 0 oa).support,
    ∀ i : spec.ι, count i ≤ qb i

-- port

end OracleComp
