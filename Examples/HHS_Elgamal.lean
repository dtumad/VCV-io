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

-- open HomogeneousSpace AsymmEncAlg

open OracleSpec OracleComp

/-- Elgemal-style encryption adapted to a homogeneous space with group structure on points.
Messages are base points in `P` (in practice this is some encoding of messages),
The public key is a pair of base points in `P` chosen uniformly at random,
and the secret key is their vectorization in `G`. Signatures are also a pair of base points. -/
def elgamalAsymmEnc (G P : Type) [SelectableType G] [SelectableType P]
    [AddGroup G] [Group P] [AddTorsor G P] : AsymmEncAlg unifSpec ProbComp
    (M := P) (PK := P × P) (SK := G) (C := P × P) where
  keygen := do
    let x₀ ←$ᵗ P
    let sk ←$ᵗ G
    return ((x₀, sk +ᵥ x₀), sk)
  encrypt := λ m (x₀, pk) ↦ do
    let g ←$ᵗ G
    return (g +ᵥ x₀, m * (g +ᵥ pk))
  decrypt := λ (c₁, c₂) sk ↦ do
    return c₂ / (sk +ᵥ c₁)
  __ := ExecutionMethod.default

-- namespace elgamalAsymmEnc

-- variable (G P : ℕ → Type) [HomogeneousSpace G P] [Π sp, Group (P sp)]

-- section sound

-- -- theorem isSound : (elgamalAsymmEnc G P).isSound := by
--   -- suffices h : ∀ sp (m x : P sp) (g₁ g₂ : G sp), m * (g₂ +ᵥ (g₁ +ᵥ x)) / (g₁ +ᵥ (g₂ +ᵥ x)) = m
--   --   by simp [AsymmEncAlg.sound_iff, h]
--   -- intros m x g₁ g₂
--   -- rw [vadd_comm, mul_div_cancel_right]

-- end sound

-- section IND_CPA

-- -- variable {G P : Type} [AddCommGroup G] [HomogeneousSpace G P] [Group P]

-- -- def IND_CPA_reduction (adv : (elgamalAsymmEnc G P).IND_CPA_Adv) : vectorizationAdv G P :=
-- --   sorry

-- -- theorem le_IND_CPA_reduction_advantage (adv : (elgamalAsymmEnc G P).IND_CPA_Adv) :
-- --     (IND_CPA_Exp adv).advantage ≤ (vectorizationExp (IND_CPA_reduction adv)).advantage := by
-- --   sorry

-- end IND_CPA

-- end elgamalAsymmEnc
