/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Constructions
import VCVio.OracleComp.SimSemantics.Append

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

-- TODO: Could think about basing things around this instead
def exec' (alg : OracleAlg spec) (n : ℕ)
    (oa : OracleComp (unifSpec ++ₒ spec n) α) : OracleComp unifSpec α :=
  simulate' (idOracle ++ₛₒ alg.baseSimOracle n) ((), alg.init_state n) oa

lemma exec_def (oa : OracleComp (spec n) α) :
    alg.exec n oa = simulate' (alg.baseSimOracle n) (alg.init_state n) oa := rfl

lemma exec'_def (oa : OracleComp (unifSpec ++ₒ spec n) α) :
    alg.exec' n oa = simulate' (idOracle ++ₛₒ alg.baseSimOracle n) ((), alg.init_state n) oa :=
  rfl

@[simp low]
lemma exec_return (x : α) : alg.exec n (return x) = return x := rfl

@[simp low]
lemma exec'_pure (x : α) : alg.exec' n (pure x) = pure x := rfl

@[simp low]
lemma exec_bind (oa : OracleComp (spec n) α) (ob : α → OracleComp (spec n) β) :
    alg.exec n (oa >>= ob) = (do
      let (x, s) ← simulate (alg.baseSimOracle n) (alg.init_state n) oa
      simulate' (alg.baseSimOracle n) s (ob x)) :=
  simulate'_bind (alg.baseSimOracle n) (alg.init_state n) oa ob

@[simp low]
lemma exec_query (alg : OracleAlg spec) (i : ι) (t : (spec n).domain i) :
    alg.exec n (query i t) = Prod.fst <$> alg.baseSimOracle n i t (alg.init_state n) :=
  simulate'_query (alg.baseSimOracle n) (alg.init_state n) i t

@[simp low]
lemma exec_map (alg : OracleAlg spec) (oa : OracleComp (spec n) α) (f : α → β) :
    alg.exec n (f <$> oa) = f <$> alg.exec n oa :=
  simulate'_map (alg.baseSimOracle n) (alg.init_state n) oa f

@[simp low]
lemma exec_seq (alg : OracleAlg spec) (oa : OracleComp (spec n) α)
    (og : OracleComp (spec n) (α → β)) : alg.exec n (og <*> oa) = (do
      let (f, s) ← simulate (alg.baseSimOracle n) (alg.init_state n) og
      f <$> simulate' (alg.baseSimOracle n) s oa) :=
  simulate'_seq (alg.baseSimOracle n) (alg.init_state n) oa og

section baseOracleAlg

/-- Simple base structure for defining algorithms using only uniform selection oracles.
Usefull to auto-fill in fields with simple defaults in this case. -/
abbrev baseOracleAlg : OracleAlg (λ _ ↦ unifSpec) where
  baseState := λ _ ↦ Unit
  init_state := λ _ ↦ ()
  baseSimOracle := λ _ ↦ idOracle

abbrev baseOracleAlg' : OracleAlg (λ _ ↦ emptySpec) where
  baseState := λ _ ↦ Unit
  init_state := λ _ ↦ ()
  baseSimOracle := λ _ ↦ unifOracle

@[simp]
lemma exec_baseOracleAlg (n : ℕ) (oa : OracleComp unifSpec α) :
    baseOracleAlg.exec n oa = oa := by
  simp only [exec_def, idOracle.simulate'_eq]

end baseOracleAlg

end OracleAlg
