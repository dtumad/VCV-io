/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio
import Mathlib.Data.Vector.Zip

/-!
# One Time Pad

This file defines and proves the perfect secrecy of the one-time pad encryption algorithm.
-/

open Mathlib OracleSpec OracleComp OracleAlg ENNReal BigOperators

/-- The one-time pad symmetric encryption algorithm, using .
Requires no oracles so the `OracleSpec` is `[]ₒ`-/
def oneTimePad : SymmEncAlg (λ _ ↦ []ₒ)
    (Vector Bool) (Vector Bool) (Vector Bool) where
  keygen := λ sp ↦ $ᵗ Vector Bool sp -- random bitvec
  encrypt := λ _ k m ↦ return m.zipWith xor k
  decrypt := λ _ k σ ↦ return σ.zipWith xor k
  __ := baseOracleAlg -- Oracles already reduced

def oneTimePad' : SymmEncAlg (λ _ ↦ []ₒ)
    BitVec BitVec BitVec where
  keygen := λ sp ↦ $ᵗ BitVec sp
  encrypt := λ _ k m ↦ return (BitVec.xor k m)
  decrypt := λ _ k σ ↦ return (BitVec.xor k σ)
  __ := baseOracleAlg

namespace oneTimePad

theorem isSound : (oneTimePad).isSound := by
  have h : ∀ n (ys xs : Vector Bool n), (ys.zipWith xor xs).zipWith xor xs = ys :=
    λ n ys xs ↦ Vector.ext (λ i ↦ by simp)
  simp only [SymmEncAlg.isSound, oneTimePad, pure_bind, h, probOutput_eq_one_iff', finSupport_bind,
    finSupport_uniformOfFintype, finSupport_pure, Finset.biUnion_subset,
    Finset.mem_univ, subset_refl, imp_self, implies_true]

end oneTimePad
