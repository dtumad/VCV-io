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

structure OracleAlg {ι : Type} (spec : ℕ → OracleSpec ι) where
  baseState (n : ℕ) : Type
  init_state (n : ℕ) : baseState n
  baseSimOracle (n : ℕ) : spec n →[baseState n]ₛₒ unifSpec

namespace OracleAlg

variable {ι : Type} {spec : ℕ → OracleSpec ι} {α β γ : Type}
  (alg : OracleAlg spec) (n : ℕ)

def exec (alg : OracleAlg spec) (n : ℕ)
    (oa : OracleComp (spec n) α) : OracleComp unifSpec α :=
  simulate' (alg.baseSimOracle n) (alg.init_state n) oa

lemma exec_def (oa : OracleComp (spec n) α) :
    alg.exec n oa = simulate' (alg.baseSimOracle n) (alg.init_state n) oa := rfl

@[simp low]
lemma exec_return (x : α) : alg.exec n (return x) = return x := rfl

-- @[simp low]
-- lemma exec_bind (alg : OracleAlg spec) (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
--     alg.exec (oa >>= ob) = (do
--       let z ← simulate alg.baseSimOracle alg.init_state oa
--       simulate' alg.baseSimOracle z.2 (ob z.1)) :=
--   simulate'_bind alg.baseSimOracle  alg.init_state oa ob

-- @[simp low]
-- lemma exec_query (alg : OracleAlg spec) (i : ι) (t : spec.domain i) :
--     alg.exec (query i t) = Prod.fst <$> alg.baseSimOracle i t alg.init_state :=
--   simulate'_query alg.baseSimOracle alg.init_state i t

-- @[simp low]
-- lemma exec_map (alg : OracleAlg spec) (oa : OracleComp spec α) (f : α → β) :
--     alg.exec (f <$> oa) = f <$> alg.exec oa :=
--   simulate'_map alg.baseSimOracle alg.init_state oa f

-- @[simp low]
-- lemma exec_seq (alg : OracleAlg spec) (oa : OracleComp spec α) (og : OracleComp spec (α → β)) :
--     alg.exec (og <*> oa) = (do
--       let (f, s) ← simulate alg.baseSimOracle alg.init_state og
--       f <$> simulate' alg.baseSimOracle s oa) :=
--   simulate'_seq alg.baseSimOracle alg.init_state oa og

section baseOracleAlg

/-- Simple base structure for defining algorithms using only uniform selection oracles.
Usefull to auto-fill in fields with simple defaults in this case. -/
@[inline, reducible]
def baseOracleAlg : OracleAlg (λ _ ↦ unifSpec) where
  baseState := λ _ ↦ Unit
  init_state := λ _ ↦ ()
  baseSimOracle := λ _ ↦ idOracle

@[simp]
lemma exec_baseOracleAlg (n : ℕ) (oa : OracleComp unifSpec α) :
    baseOracleAlg.exec n oa = oa := by
  simp only [exec_def, idOracle.simulate'_eq]

end baseOracleAlg

end OracleAlg
