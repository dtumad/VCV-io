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

structure SymmEncAlg' {ι : Type} (spec : OracleSpec ι) (σ M K C : Type)
    extends OracleImpl spec σ where
  keygen : OracleComp (unifSpec ++ₒ spec) K
  encrypt (k : K) (m : M) : OracleComp (unifSpec ++ₒ spec) C
  decrypt (k : K) (c : C) : OracleComp (unifSpec ++ₒ spec) M

structure SymmEncAlg {ι : Type} (spec : ℕ → OracleSpec ι) (M K C : ℕ → Type)
    extends OracleAlg spec where
  (keygen (sp : ℕ) : OracleComp (unifSpec ++ₒ spec sp) (K sp))
  (encrypt (sp : ℕ) : K sp → M sp → OracleComp (unifSpec ++ₒ spec sp) (C sp))
  (decrypt (sp : ℕ) : K sp → C sp → OracleComp (unifSpec ++ₒ spec sp) (M sp))

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

def isSound' {ι : Type} {spec : OracleSpec ι} {σ M K C : Type}
    (encAlg : SymmEncAlg' spec σ M K C) : Prop :=
  ∀ m : M, [= m | Prod.fst <$> (encAlg.exec do
    let k : K ← encAlg.keygen
    let σ ← encAlg.encrypt k m
    encAlg.decrypt k σ)] = 1

variable (encAlg : SymmEncAlg spec M K C)

-- lemma isSound_iff {ι : Type} {spec : OracleSpec ι} {M K C : Type}
--     (encAlg : SymmEncAlg' spec M K C) : encAlg.isSound ↔
--     ∀ m : M, ()

-- lemma isSound_iff_forall_mem_support :

end isSound

-- section perfectSecrecy



-- end perfectSecrecy

end SymmEncAlg
