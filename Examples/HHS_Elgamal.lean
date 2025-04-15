/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio

/-!
# ElGamal Encryption

This file defines an anologue of the ElGamal Encryption scheme and proves it is IND-CPA secure
We use `AddTorsor` as a natural analogue to a hard homogeneous space, which gives the
standard ElGamal algorithm when the group action is exponentiation in a finite field.
-/

open OracleSpec OracleComp

/-- Elgemal-style encryption adapted to a homogeneous space with group structure on points.
Messages are base points in `P` (in practice this is some encoding of messages),
The public key is a pair of base points in `P` chosen uniformly at random,
and the secret key is their vectorization in `G`. Signatures are also a pair of base points. -/
@[simps!] def elgamalAsymmEnc (G P : Type) [SelectableType G] [SelectableType P]
    [AddGroup G] [Group P] [AddTorsor G P] : AsymmEncAlg ProbComp
    (M := P) (PK := P × P) (SK := G) (C := P × P) where
  keygen := do
    let x₀ ←$ᵗ P; let sk ←$ᵗ G
    return ((x₀, sk +ᵥ x₀), sk)
  encrypt := fun (x₀, pk) msg => do
    let g ←$ᵗ G
    return (g +ᵥ x₀, msg * (g +ᵥ pk))
  decrypt := fun sk (c₁, c₂) => do
    return c₂ / (sk +ᵥ c₁)
  __ := ExecutionMethod.default

namespace elgamalAsymmEnc

variable {G P : Type} [SelectableType G] [SelectableType P]
    [AddCommGroup G] [Group P] [AddTorsor G P]

@[simp] lemma toExecutionMethod_eq :
    (elgamalAsymmEnc G P).toExecutionMethod = ExecutionMethod.default := rfl

theorem Correct [DecidableEq P] : (elgamalAsymmEnc G P).PerfectlyCorrect := by
  have : ∀ (msg x : P) (g₁ g₂ : G), msg * (g₂ +ᵥ (g₁ +ᵥ x)) / (g₁ +ᵥ (g₂ +ᵥ x)) = msg :=
    fun m x g₁ g₂ => by rw [vadd_comm g₁ g₂ x, mul_div_cancel_right]
  simp [this]
  sorry -- neverFails api

end elgamalAsymmEnc
