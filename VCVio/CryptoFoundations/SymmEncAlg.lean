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

open OracleSpec OracleComp OracleAlg BigOperators

structure SymmEncAlg {ι : Type} (spec : ℕ → OracleSpec ι) (M K C : ℕ → Type)
    extends OracleAlg spec where
  (keygen (sp : ℕ) : OracleComp (spec sp) (K sp))
  (encrypt (sp : ℕ) : K sp → M sp → OracleComp (spec sp) (C sp))
  (decrypt (sp : ℕ) : K sp → C sp → OracleComp (spec sp) (M sp))

namespace SymmEncAlg

variable {ι : Type} {spec : ℕ → OracleSpec ι} {M K C : ℕ → Type}

section isSound

variable [Π sp, DecidableEq (M sp)]

/-- A symmetric encryption algorithm is sound is messages decrypt to themselves given a random key.
Note that we assume the algorithm never fails, although in general this could be modified
to allow for a (negligible) chance of encryption failure. -/
def isSound (encAlg : SymmEncAlg spec M K C) : Prop :=
  ∀ sp : ℕ, ∀ m : M sp, [= m | do
    let k ← encAlg.keygen sp
    let σ ← encAlg.encrypt sp k m
    encAlg.decrypt sp k σ] = 1

variable (encAlg : SymmEncAlg spec M K C)

-- lemma isSound_iff_forall_mem_support :

end isSound

-- section perfectSecrecy



-- end perfectSecrecy

end SymmEncAlg
