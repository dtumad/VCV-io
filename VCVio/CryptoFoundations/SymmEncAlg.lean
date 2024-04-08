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

structure SymmEncAlg (spec : OracleSpec) (M K C : Type)
  extends OracleAlg spec :=
(keygen : Unit → OracleComp spec K)
(encrypt : M → K → OracleComp spec C)
(decrypt : C → K → OracleComp spec M)

namespace SymmEncAlg

section sound

variable {spec : OracleSpec} {M PK SK C : Type} [DecidableEq M]


variable [DecidableEq M]

/-- Experiment for checking that an asymmetric encryption algorithm is sound,
i.e. that decryption properly reverses encryption -/
def soundnessExp (encAlg : SymmEncAlg spec M K C) (m : M) :
    SecExp spec K where
  inpGen := encAlg.keygen ()
  main := λ k ↦ do
    let σ ← encAlg.encrypt m k
    let m' ← encAlg.decrypt σ k
    return m = m'
  __ := encAlg

/-- An asymmetric encryption algorithm is sound if messages always decrypt to themselves. -/
def isSound (encAlg : SymmEncAlg spec M K C) : Prop :=
  ∀ m : M, (soundnessExp encAlg m).advantage = 1

end sound

end SymmEncAlg
