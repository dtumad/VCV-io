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

open OracleSpec OracleComp

structure OracleAlg (spec : OracleSpec) where
  baseState : Type
  init_state : baseState
  baseSimOracle : spec →[baseState]ₛₒ unifSpec

namespace OracleAlg

variable {spec : OracleSpec} {α β γ : Type}

def exec (alg : OracleAlg spec) (oa : OracleComp spec α) : OracleComp unifSpec α :=
  simulate' alg.baseSimOracle oa alg.init_state

lemma exec.def (alg : OracleAlg spec) (α : Type) :
    alg.exec (α := α) = (simulate' alg.baseSimOracle · alg.init_state) := rfl

@[simp low]
lemma exec_pure (alg : OracleAlg spec) (x : α) : alg.exec (pure x) = pure x := rfl

@[simp low]
lemma exec_bind (alg : OracleAlg spec) (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    alg.exec (oa >>= ob) = (do
      let z ← simulate alg.baseSimOracle oa alg.init_state
      simulate' alg.baseSimOracle (ob z.1) z.2) :=
  simulate'_bind alg.baseSimOracle oa ob alg.init_state

@[simp low]
lemma exec_query (alg : OracleAlg spec) (i : spec.ι) (t : spec.domain i) :
    alg.exec (query i t) = Prod.fst <$> alg.baseSimOracle i t alg.init_state :=
  simulate'_query alg.baseSimOracle i t alg.init_state

@[simp low]
lemma exec_map (alg : OracleAlg spec) (oa : OracleComp spec α) (f : α → β) :
    alg.exec (f <$> oa) = f <$> alg.exec oa :=
  simulate'_map alg.baseSimOracle oa f alg.init_state

@[simp low]
lemma exec_seq (alg : OracleAlg spec) (oa : OracleComp spec α) (og : OracleComp spec (α → β)) :
    alg.exec (og <*> oa) = (simulate alg.baseSimOracle og alg.init_state >>= λ ⟨f, s⟩ ↦
      f <$> simulate' alg.baseSimOracle oa s) :=
  simulate'_seq alg.baseSimOracle oa og

section baseOracleAlg

/-- Simple base structure for defining algorithms using only uniform selection oracles.
Usefull to auto-fill in fields with simple defaults in this case. -/
-- @[inline, reducible]
def baseOracleAlg : OracleAlg unifSpec where
  baseState := Unit
  init_state := ()
  baseSimOracle := idOracle

@[simp]
lemma exec_baseOracleAlg (oa : OracleComp unifSpec α) :
    baseOracleAlg.exec oa = oa := by
  simp only [baseOracleAlg, exec.def, idOracle.simulate'_eq]

end baseOracleAlg

end OracleAlg
