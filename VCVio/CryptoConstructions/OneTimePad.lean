/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SymmEncAlg
import VCVio.OracleComp.Constructions.Replicate
import Mathlib.Data.Vector.Zip

/-!
# One Time Pad

This file defines and proves the security of the one-time pad encryption algorithm.
-/

open OracleSpec OracleComp OracleAlg ENNReal BigOperators

def oneTimePad (n : ℕ) : SymmEncAlg unifSpec
    (Vector Bool n) (Vector Bool n) (Vector Bool n) where
  keygen := λ _ ↦ replicate ($ᵗ Bool) n
  encrypt := λ m k ↦ return m.zipWith xor k
  decrypt := λ σ k ↦ return σ.zipWith xor k
  __ := OracleAlg.baseOracleAlg

namespace oneTimePad

theorem isSound (n : ℕ) : (oneTimePad n).isSound := by
  intro m
  simp [oneTimePad, SymmEncAlg.soundnessExp]
  sorry
  -- simp [Vector.zipWith_a

def testOTP {n : ℕ} (m : Vector Bool n) : IO Unit := do
  IO.println ("Initial Message: " ++ toString m.toList)
  let k ← ((oneTimePad n).keygen ()).runIO
  IO.println ("Key: " ++ toString k.toList)
  let σ ← ((oneTimePad n).encrypt m k).runIO
  IO.println ("Ciphertext: " ++ toString σ.toList)
  let m' ← ((oneTimePad n).decrypt σ k).runIO
  IO.println ("Final Message: " ++ toString m'.toList)
  return ()

-- #eval testOTP (true ::ᵥ true ::ᵥ true ::ᵥ true ::ᵥ Vector.nil)

end oneTimePad
