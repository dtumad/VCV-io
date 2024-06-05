/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio

/-!
# ElGamal Encryption

This file defines an anologue of the ElGamal Encryption scheme and proves it is IND-CPA secure
-/

open HomogeneousSpace AsymmEncAlg

/-- Elgemal-style encryption adapted to a homogeneous space with group structure on points.
Messages are base points in `P` (in practice this is some encoding of messages),
The public key is a pair of base points in `P` chosen uniformly at random,
and the secret key is their vectorization in `G`. Signatures are also a pair of base points. -/
@[simps]
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
    return c₂ / (sk +ᵥ c₁)
  __ := OracleAlg.baseOracleAlg

namespace elgamalAsymmEnc

theorem isSound (G P : Type) [AddCommGroup G] [HomogeneousSpace G P] [Group P] :
    (elgamalAsymmEnc G P).isSound := by
  suffices h : ∀ (m x : P) (g₁ g₂ : G), m * (g₂ +ᵥ (g₁ +ᵥ x)) / (g₁ +ᵥ (g₂ +ᵥ x)) = m
    by simp [AsymmEncAlg.sound_iff, h]
  intros m x g₁ g₂
  rw [vadd_comm, mul_div_cancel_right]

section IND_CPA

variable {G P : Type} [AddCommGroup G] [HomogeneousSpace G P] [Group P]

def IND_CPA_reduction (adv : (elgamalAsymmEnc G P).IND_CPA_Adv) : vectorizationAdv G P :=
  sorry

theorem le_IND_CPA_reduction_advantage (adv : (elgamalAsymmEnc G P).IND_CPA_Adv) :
    (IND_CPA_Exp adv).advantage ≤ (vectorizationExp (IND_CPA_reduction adv)).advantage := by
  sorry

end IND_CPA

end elgamalAsymmEnc
