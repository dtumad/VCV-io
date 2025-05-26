/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.SimSemantics.Distinguisher
import VCVio.OracleComp.Constructions.UniformSelect

/-!
# Symmetric Encryption Schemes.

This file defines a type `SymmEncAlg spec M K C` to represent a protocol
for symmetric encryption using oracles in `spec`, with message space `M`,
secret keys of type `K`, and ciphertext space `C`.
-/

universe u v w

open OracleSpec OracleComp ENNReal

/-- Symmetric encryption algorithm with access to oracles in `spec` (simulated with state `σ`),
where `M` is the space of messages, `K` is the key space, and `C` is the ciphertext space. -/
structure SymmEncAlg (m : Type u → Type v)
    (M K C : Type u) extends ExecutionMethod m where
  keygen : m K
  encrypt (k : K) (msg : M) : m C
  decrypt (k : K) (c : C) : Option M

structure SymmEncAlg' (m : Type u → Type v) (M K C : ℕ → Type u)
    extends ExecutionMethod m where
  keygen (sp : ℕ) : m (K sp)
  encrypt {sp : ℕ} (k : K sp) (msg : M sp) : m (C sp)
  decrypt {sp : ℕ} (k : K sp) (c : C sp) : Option (M sp)

namespace SymmEncAlg

variable {ι : Type w} {spec : OracleSpec ι} {m : Type → Type v} {M K C : Type}
    [AlternativeMonad m] [LawfulAlternative m]

section correct

variable [DecidableEq M]

/-- A `SymmEncAlg` is complete if decrypting an encrypted message always returns that original
message, captured here by a `guard` statement. -/
class Correct (encAlg : SymmEncAlg m M K C) : Prop where
  decrypt_encrypt_eq_message (msg : M) : [= some msg | encAlg.exec do
    let k ← encAlg.keygen
    return encAlg.decrypt k (← encAlg.encrypt k msg)] = 1

end correct

section OneTimeUniformCiphertexts

variable [SelectableType C] [Fintype C] [Inhabited C]

def OneTimeUniformCiphers (encAlg : SymmEncAlg ProbComp M K C) : Prop :=
  let realImpl : QueryImpl (M →ₒ C) ProbComp :=
    QueryImpl.ofFn fun m => do encAlg.encrypt (← encAlg.keygen) m
  let idealImpl : QueryImpl (M →ₒ C) ProbComp :=
    QueryImpl.ofFn fun _ => do $ᵗ C
  realImpl ≃ₛₒ idealImpl

end OneTimeUniformCiphertexts

section OneTimeSecrecy

def OneTimeSecrecy (encAlg : SymmEncAlg ProbComp M K C) : Prop :=
  let realImpl : QueryImpl (M × M →ₒ C) ProbComp :=
    QueryImpl.ofFn fun ms => do encAlg.encrypt (← encAlg.keygen) ms.1
  let idealImpl : QueryImpl (M × M →ₒ C) ProbComp :=
    QueryImpl.ofFn fun ms => do encAlg.encrypt (← encAlg.keygen) ms.2
  realImpl ≃ₛₒ idealImpl

theorem oneTimeSecrecy_of_oneTimeUniformCiphers [SelectableType C]
    [Fintype C] [Inhabited C] (encAlg : SymmEncAlg ProbComp M K C)
    (h : OneTimeUniformCiphers encAlg) : OneTimeSecrecy encAlg := by
  unfold OneTimeSecrecy
  unfold OneTimeUniformCiphers at h

  -- unfold OneTimeSecrecy
  simp only [] at *
  sorry

  -- simp only [] at h
  -- calc _
    -- _ ≃ₛₒ _ := h
    -- _ ≃ₛₒ _ := sorry
  -- refine trans ?_ (h.trans ?_)
  --
  -- intro adv
  -- specialize h adv
  -- simp
  -- sorry

end OneTimeSecrecy

section perfectSecrecy

def perfectSecrecy (encAlg : SymmEncAlg m M K C) : Prop :=
  ∀ mgen : ProbComp M, ∀ msg : M, ∀ σ : C,
    [= (msg, σ) | encAlg.exec do
      let msg' ← encAlg.lift_probComp mgen
      (msg', ·) <$> encAlg.encrypt (← encAlg.keygen) msg'] =
    [= msg | mgen]

/-- Shanon's theorem on perfect secrecy, showing that encryption and decryption must be determined
bijections between message and cipher-text space, and that keys must be chosen uniformly. -/
theorem perfectSecrecy_iff_of_card_eq [Fintype M] [Fintype K] [Fintype C]
    (encAlg : SymmEncAlg m M K C) [encAlg.Correct] (h1 : Fintype.card M = Fintype.card K)
    (h2 : Fintype.card K = Fintype.card C) : encAlg.perfectSecrecy ↔
      (∀ k, [= k | encAlg.exec encAlg.keygen] = (Fintype.card K : ℝ≥0∞)⁻¹) ∧
      (∀ m c, ∃! k, k ∈ (encAlg.exec encAlg.keygen).support ∧ encAlg.encrypt k m = c) :=
  sorry

end perfectSecrecy

end SymmEncAlg
