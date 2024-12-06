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
The only oracles needed are `unifSpec`, which requires no implementation. -/
@[simps!] def oneTimePad (n : ℕ) : SymmEncAlg unifSpec Unit
    (M := BitVec n) (K := BitVec n) (C := BitVec n) where
  keygen := $ᵗ BitVec n -- Generate a key by choosing a random bit-vector
  encrypt k m := return k ^^^ m -- encrypt by xor-ing with the key
  decrypt k σ := return k ^^^ σ -- decrypt by xor-ing with the key
  __ := defaultImpl -- No oracles to implement so use default

namespace oneTimePad

theorem isComplete (n : ℕ) : (oneTimePad n).isComplete :=
  λ m ↦ by simp [SymmEncAlg.soundnessExp]
  -- λ m ↦  by simp only [SymmEncAlg.soundnessExp, oneTimePad_keygen, oneTimePad_encrypt,
  --   oneTimePad_decrypt, guard_eq, pure_bind, BitVec.xor_self_xor, ↓reduceIte, bind_pure_comp,
  --   SecExp.advantage_eq_one_iff, simulate_map, oneTimePad_baseSimOracle, oneTimePad_init_state,
  --   idOracle.simulate_eq, Functor.map_map, Prod.map_apply, id_eq, probFailure_map,
  --   probFailure_uniformOfFintype]

end oneTimePad
