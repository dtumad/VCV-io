/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.UniformSelect

/-!
# Symmetric Encryption Schemes.

This file defines a type `SymmEncAlg spec M K C` to represent a protocol
for symmetric encryption using oracles in `spec`, with message space `M`,
secret keys of type `K`, and ciphertext space `C`.
-/

universe u v w

open OracleSpec OracleComp

/-- Symmetric encryption algorithm with access to oracles in `spec` (simulated with state `σ`),
where `M` is the space of messages, `K` is the key space, and `C` is the ciphertext space. -/
structure SymmEncAlg {ι : Type w} (spec : OracleSpec ι) (em : Type → Type v) (M K C : Type u)
    extends ExecutionMethod spec em where
  keygen : OracleComp spec K
  encrypt (k : K) (m : M) : OracleComp spec C
  decrypt (k : K) (c : C) : OracleComp spec M

namespace SymmEncAlg

variable {ι : Type w} {spec : OracleSpec ι} {em : Type → Type v} {M K C : Type}
    [AlternativeMonad em] [LawfulAlternative em]

section sound

variable [DecidableEq M]

/-- Experiment to check that an encryption and decryption are inverses of each other. -/
def soundnessExp (encAlg : SymmEncAlg spec em M K C)
    (m : M) : SecExp spec em where
  main := do
    let k ← encAlg.keygen
    let σ ← encAlg.encrypt k m
    let m' ← encAlg.decrypt k σ
    guard (m' = m)
  __ := encAlg

/-- A symmetric encryption algorithm is complete if correctly generated ciphertexts
always decrypt to the original plaintext. -/
def isComplete (encAlg : SymmEncAlg spec em M K C) : Prop :=
  ∀ m : M, (soundnessExp encAlg m).advantage = 1

end sound

end SymmEncAlg
