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

structure SymmEncAlg {ι : Type} (spec : OracleSpec ι) (M K C : Type)
  extends OracleAlg spec :=
(keygen : Unit → OracleComp spec K)
(encrypt : M → K → OracleComp spec C)
(decrypt : C → K → OracleComp spec M)

namespace SymmEncAlg

variable {ι : Type} {spec : OracleSpec ι} {M K C : Type}

section sound

variable [DecidableEq M]

/-- Experiment for checking that a symmetric encryption algorithm is sound,
i.e. that decryption properly reverses encryption -/
@[simp]
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

variable (encAlg : SymmEncAlg spec M K C)

@[simp]
lemma isSound_iff_forall (encAlg : SymmEncAlg spec M K C) :
    encAlg.isSound ↔ ∀ m : M, (encAlg.exec (do
      let k ← encAlg.keygen ()
      let σ ← encAlg.encrypt m k
      encAlg.decrypt σ k)).support ⊆ {m} := by
  refine forall_congr' (λ m ↦ ?_)
  simp only [soundnessExp, @eq_comm _ m, bind_pure_comp, ← map_bind, SecExp.advantage_eq_one_iff,
    exec_map, exec_bind, simulate'_bind, support_map, support_bind, Set.mem_image, Set.mem_iUnion,
    exists_prop, Prod.exists, decide_eq_false_iff_not, not_exists, not_and, not_not,
    forall_exists_index, and_imp, Set.subset_singleton_iff]

end sound

section perfectSecrecy



end perfectSecrecy

end SymmEncAlg
