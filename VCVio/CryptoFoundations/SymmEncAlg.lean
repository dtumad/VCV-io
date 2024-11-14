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

open OracleSpec OracleComp Prod

structure SymmEncAlg {ι : Type} (spec : OracleSpec ι) (σ M K C : Type)
    extends OracleImpl spec σ where
  keygen : OracleComp (unifSpec ++ₒ spec) K
  encrypt (k : K) (m : M) : OracleComp (unifSpec ++ₒ spec) C
  decrypt (k : K) (c : C) : OracleComp (unifSpec ++ₒ spec) M

namespace SymmEncAlg

variable {ι : Type} {spec : OracleSpec ι} {σ M K C : Type}

section isSound

/-- A symmetric encryption algorithm is sound is messages decrypt to themselves given a random key.
Note that we assume the algorithm never fails, although in general this could be modified
to allow for a (negligible) chance of encryption failure. -/
def isSound (encAlg : SymmEncAlg spec σ M K C) : Prop :=
  ∀ m : M, [= m | fst <$> encAlg.exec do
    let k : K ← encAlg.keygen
    let σ ← encAlg.encrypt k m
    encAlg.decrypt k σ] = 1

end isSound

end SymmEncAlg
