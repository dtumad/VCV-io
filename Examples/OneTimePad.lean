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

open Mathlib OracleSpec OracleComp OracleImpl ENNReal BigOperators

/-- The one-time pad symmetric encryption algorithm, using `BitVec`s as keys and messages.
Encryption and decryption both just apply `BitVec.xor` with the key.
Requires no oracles so the `OracleSpec` is always `[]ₒ`. -/
def oneTimePad (n : ℕ) : SymmEncAlg unifSpec Unit
    (M := BitVec n) (K := BitVec n) (C := BitVec n) where
  keygen := $ᵗ BitVec n
  encrypt k m := return k ^^^ m
  decrypt k σ := return k ^^^ σ
  __ := defaultImpl

namespace oneTimePad

-- @[simp]
-- lemma keygen_def (n : ℕ) : (oneTimePad n).keygen = $ᵗ BitVec n := rfl

-- @[simp]
-- lemma encrypt_def (n : ℕ) : (oneTime)

-- @[simp]
-- lemma encrypt_bind_decrypt {n : ℕ} (k m : BitVec n) :
--     do {let σ ← (oneTimePad n).encrypt k m; (oneTimePad n).decrypt k σ} = return m := by
--   simp [oneTimePad]

theorem isSound (n : ℕ) : (oneTimePad n).isSound :=
  λ m ↦ probOutput_eq_one (by simp [oneTimePad])

end oneTimePad
