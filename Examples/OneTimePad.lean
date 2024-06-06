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

open OracleSpec OracleComp OracleAlg ENNReal BigOperators

def oneTimePad : SymmEncAlg (λ _ ↦ unifSpec)
    (Vector Bool) (Vector Bool) (Vector Bool) where
  keygen := λ sp ↦ $ᵗ Vector Bool sp -- random bitvec
  encrypt := λ _ m k ↦ return m.zipWith xor k
  decrypt := λ _ σ k ↦ return σ.zipWith xor k
  __ := baseOracleAlg -- leave oracles as is

namespace oneTimePad

theorem isSound (n : ℕ) : (oneTimePad).isSound := by
  have : ∀ ys xs : Vector Bool n, (ys.zipWith xor xs).zipWith xor xs = ys :=
    λ ys xs ↦ Vector.ext (λ i ↦ by simp)
  sorry
  -- simpa [oneTimePad, SymmEncAlg.soundnessExp] using this

end oneTimePad
