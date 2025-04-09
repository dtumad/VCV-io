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
@[simps!] def oneTimePad (n : ℕ) : SymmEncAlg ProbComp
    (M := BitVec n) (K := BitVec n) (C := BitVec n) where
  keygen := $ᵗ BitVec n -- Generate a key by choosing a random bit-vector
  encrypt k m := return k ^^^ m -- encrypt by xor-ing with the key
  decrypt k σ := some (k ^^^ σ) -- decrypt by xor-ing with the key
  __ := ExecutionMethod.default -- No oracles to implement so use default

namespace oneTimePad

@[simp] lemma toExecutionMethod_eq (n : ℕ) :
    (oneTimePad n).toExecutionMethod = ExecutionMethod.default := rfl

/-- Encryption and decryption are inverses for any OTP key. -/
instance complete (n : ℕ) : (oneTimePad n).Complete := ⟨by simp⟩

-- [Pred | Computation]
example : [fun (x, y) => x + y = 0 | do
    let x : ℕ ← $[0..9]
    let y : ℕ ← $[0..9]
    return (x, y)] = 1 / 100 := sorry


example (mx : PMF ℕ) :
    let comp : PMF ℕ := mx.bind (fun x =>
      (PMF.bernoulli 2⁻¹ (by simp)).bind fun b =>
      PMF.pure (if b then 2 * x else 2 * x + 1))
    comp.toOuterMeasure {n | Even n} = 1 / 2 :=
  sorry

example (mx : ProbComp ℕ) :
    let comp : ProbComp ℕ := do
      let x ← mx
      return (if (←$ᵗ Bool) then 2 * x else 2 * x + 1)
    [Even | comp] = (1 - [⊥ | mx]) * 2⁻¹ := by
  simp [probEvent_bind_eq_tsum, apply_ite,
    ENNReal.tsum_mul_right, tsum_probOutput_eq_sub]

end oneTimePad
