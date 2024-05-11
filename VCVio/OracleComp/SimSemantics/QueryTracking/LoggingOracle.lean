/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Simulate

/-!
# Logging Queries Made by a Computation

-/

namespace OracleSpec

/-- Log of oracle queries represented by lists of input output pairs,
parameterized by the set of oracles available. -/
def QueryLog {ι : Type} (spec : OracleSpec ι) : Type :=
  (i : ι) → List (spec.domain i × spec.range i)

variable {ι : Type}

/-- Update a query log by adding a new element to the appropriate list.
Note that this requires decidable equality on the indexing set. -/
def QueryLog.logQuery [DecidableEq ι] {spec : OracleSpec ι} (log : QueryLog spec) {i : ι}
    (t : spec.domain i) (u : spec.range i) : QueryLog spec :=
  Function.update log i ((t, u) :: log i)

/-- Check if an element was ever queried in a log of queries.
Relies on decidable equality of the domain types of oracles. -/
def QueryLog.wasQueried {spec : OracleSpec ι} (log : QueryLog spec)
    (i : ι) (t : spec.domain i) : Bool :=
  match (log i).find? (λ (t', _) ↦ t = t') with
  | Option.some _ => true
  | Option.none => false

end OracleSpec

open OracleComp OracleSpec

/-- Simulation oracle for tracking the quries in a `QueryLog`, without modifying the actual
behavior of the oracle. Requires decidable equality of the indexing set to determine
which list to update when queries come in. -/
def loggingOracle {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} :
    spec →[QueryLog spec]ₛₒ spec :=
  λ i t log ↦ do let u ← query i t; return (u, log.logQuery t u)
