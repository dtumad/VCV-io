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

open Mathlib OracleSpec OracleComp ENNReal BigOperators

/-- The one-time pad symmetric encryption algorithm, using `BitVec`s as keys and messages.
Encryption and decryption both just apply `BitVec.xor` with the key.
The only oracles needed are `unifSpec`, which requires no implementation. -/
@[simps!] def oneTimePad (n : ℕ) : SymmEncAlg unifSpec ProbComp
    (M := BitVec n) (K := BitVec n) (C := BitVec n) where
  keygen := $ᵗ BitVec n -- Generate a key by choosing a random bit-vector
  encrypt k m := return k ^^^ m -- encrypt by xor-ing with the key
  decrypt k σ := return k ^^^ σ -- decrypt by xor-ing with the key
  __ := ExecutionMethod.default -- No oracles to implement so use default

namespace oneTimePad

theorem isComplete (n : ℕ) : (oneTimePad n).isComplete :=
  λ m ↦ by {
    simp [SymmEncAlg.soundnessExp, oneTimePad]

    sorry
  }

end oneTimePad
