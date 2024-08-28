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

/-- The one-time pad symmetric encryption algorithm, using `BitVec`s as keys and messages.
Encryption and decryption both just apply `BitVec.xor` with the key.
Requires no oracles so the `OracleSpec` is always `[]ₒ`. -/
def oneTimePad : SymmEncAlg (λ _ ↦ []ₒ)
    BitVec BitVec BitVec where
  keygen n := $ᵗ BitVec n
  encrypt _ k m := return k ^^^ m
  decrypt _ k σ := return k ^^^ σ
  __ := baseOracleAlg

namespace oneTimePad

theorem isSound : oneTimePad.isSound := by
  simp [SymmEncAlg.isSound, oneTimePad, Finset.ext_iff]

end oneTimePad
