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

def QueryLog (spec : OracleSpec) : Type :=
  (i : spec.ι) → List (spec.domain i × spec.range i)

def QueryLog.logQuery {spec : OracleSpec} (log : QueryLog spec) {i : spec.ι}
    (t : spec.domain i) (u : spec.range i) : QueryLog spec :=
  Function.update log i ((t, u) :: log i)

end OracleSpec

open OracleComp OracleSpec

def loggingOracle {spec : OracleSpec} :
    spec →[QueryLog spec]ₛₒ spec :=
  λ i t log ↦ do
    let u ← query i t
    return (u, log.logQuery t u)
