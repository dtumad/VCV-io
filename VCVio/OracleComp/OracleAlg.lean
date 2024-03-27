/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Constructions

/-!
# Structuring Protocols with Oracle Access

This file defines a structure `OracleAlg` to "extend" `OracleComp` with a `SimOracle`,
to represent the "intended" behavior of the algorithms.
By defining this as a structure we are able to then extend it in order to define protocols
that are made of multiple functions all sharing some set of oracles.

The function `OracleAlg.exec` can then be used to properly "execute" a compuation
according to the specified simulation oracle
-/

structure OracleAlg (spec : OracleSpec) where
  baseState : Type
  initState : baseState
  baseSimOracle : spec →[baseState]ₛₒ unifSpec

namespace OracleAlg

variable {spec : OracleSpec} {α β γ : Type}

-- @[inline, reducible]
def exec (alg : OracleAlg spec) (oa : OracleComp spec α) : OracleComp unifSpec α :=
  simulate' alg.baseSimOracle oa alg.initState

end OracleAlg

/-- Simple base structure for defining algorithms using only uniform selection oracles.
Usefull to auto-fill in fields with simple defaults in this case. -/
def baseOracleAlg : OracleAlg unifSpec where
  baseState := Unit
  initState := ()
  baseSimOracle := idOracle
