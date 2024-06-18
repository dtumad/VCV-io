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

structure SymmEncAlg {ι : Type}
    (spec : ℕ → OracleSpec ι) (M K C : ℕ → Type)
    extends OracleAlg spec where
  (keygen (sp : ℕ) : OracleComp (spec sp) (K sp))
  (encrypt (sp : ℕ) : M sp → K sp → OracleComp (spec sp) (C sp))
  (decrypt (sp : ℕ) : C sp → K sp → OracleComp (spec sp) (M sp))

namespace SymmEncAlg

variable {ι : Type} {spec : ℕ → OracleSpec ι} {M K C : ℕ → Type}

section sound

variable [Π sp, DecidableEq (M sp)]

/-- Experiment for checking that a symmetric encryption algorithm is sound,
i.e. that decryption properly reverses encryption -/
@[simp]
def soundnessExp (encAlg : SymmEncAlg spec M K C)
    (mDist : (sp : ℕ) → OracleComp (spec sp) (M sp)) :
    SecExp spec where
  main := λ sp ↦ do
    let m ← mDist sp
    let k ← encAlg.keygen sp
    let σ ← encAlg.encrypt sp m k
    let m' ← encAlg.decrypt sp σ k
    return m = m'
  __ := encAlg

/-- An asymmetric encryption algorithm is sound if messages always decrypt to themselves. -/
def isSound (encAlg : SymmEncAlg spec M K C) : Prop :=
  ∀ mDist, negligible (1 - (soundnessExp encAlg mDist).advantage)

variable (encAlg : SymmEncAlg spec M K C)

@[simp]
lemma isSound_iff_forall (encAlg : SymmEncAlg spec M K C) :
    encAlg.isSound ↔ ∀ sp : ℕ, ∀ m : M sp, (encAlg.exec sp (do
      let k ← encAlg.keygen sp
      let σ ← encAlg.encrypt sp m k
      encAlg.decrypt sp σ k)).support ⊆ {m} := by
  sorry
  -- refine forall_congr' (λ m ↦ ?_)
  -- simp only [soundnessExp, @eq_comm _ m, bind_pure_comp, ← map_bind, SecExp.advantage_eq_one_iff,
  --   exec_map, exec_bind, simulate'_bind, support_map,
  -- support_bind, Set.mem_image, Set.mem_iUnion,
  --   exists_prop, Prod.exists, decide_eq_false_iff_not, not_exists, not_and, not_not,
  --   forall_exists_index, and_imp, Set.subset_singleton_iff]

end sound

section perfectSecrecy



end perfectSecrecy

end SymmEncAlg
