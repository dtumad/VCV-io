/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.HardnessAssumptions.HardHomogeneousSpace
import VCVio.CryptoFoundations.AsymmEncAlg


/-!
# ElGamal Encryption

This file defines an anologue of the ElGamal Encryption scheme and proves it is IND-CPA secure
-/

/-- Elgemal-style encryption adapted to a homogeneous space with group structure on points.
Messages are base points in `P` (in practice this is some encoding of messages),
The public key is a pair of base points in `P` chosen uniformly at random,
and the secret key is their vectorization in `G`. Signatures are also a pair of base points. -/
noncomputable def elgamalAsymmEnc (G P : Type)
    [AddCommGroup G] [HomogeneousSpace G P] [Group P] :
    AsymmEncAlg unifSpec P (P × P) G (P × P) where
  keygen := λ () ↦ do
    let x₀ ← $ᵗ P
    let sk ← $ᵗ G
    let pk := sk +ᵥ x₀
    return ((x₀, pk), sk)
  encrypt := λ m ⟨x₀, pk⟩ ↦ do
    let g ← $ᵗ G
    return (g +ᵥ x₀, m * (g +ᵥ pk))
  decrypt := λ ⟨c₁, c₂⟩ sk ↦ do
    return (c₂ / (sk +ᵥ c₁))
  __ := OracleAlg.baseOracleAlg

namespace elgamalAsymmEnc

theorem elgamalAsymmEnc_sound (G P : Type)
    [AddCommGroup G] [HomogeneousSpace G P] [Group P] :
    (elgamalAsymmEnc G P).sound := by
  suffices h : ∀ (m x : P) (g₁ g₂ : G), m = m * (g₂ +ᵥ (g₁ +ᵥ x)) / (g₁ +ᵥ (g₂ +ᵥ x)) by

    simpa only [AsymmEncAlg.sound, AsymmEncAlg.soundnessExp, elgamalAsymmEnc, pure_bind, bind_assoc,
      SecExp.advantage_eq_one_iff, OracleAlg.exec_baseOracleAlg, OracleComp.support_bind,
      OracleComp.support_uniformOfFintype, Set.mem_univ, OracleComp.support_pure, Set.iUnion_true,
      Set.iUnion_singleton_eq_range, Set.mem_iUnion, Set.mem_range, decide_eq_false_iff_not,
      not_exists, not_not, h]


  sorry

end elgamalAsymmEnc
