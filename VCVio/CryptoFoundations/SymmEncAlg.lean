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

universe u v w

open OracleSpec OracleComp

/-- Symmetric encryption algorithm with access to oracles in `spec` (simulated with state `σ`),
where `M` is the space of messages, `K` is the key space, and `C` is the ciphertext space. -/
structure SymmEncAlg {ι : Type w} (spec : OracleSpec ι) (em : Type → Type v) (M K C : Type u)
    extends ExecutionMethod spec em where
  keygen : OracleComp spec K
  encrypt (k : K) (m : M) : OracleComp spec C
  decrypt : K → C → Option M

namespace SymmEncAlg

variable {ι : Type w} {spec : OracleSpec ι} {em : Type → Type v} {M K C : Type}
    [AlternativeMonad em] [LawfulAlternative em]

section sound

variable [DecidableEq M]

/-- A `SymmEncAlg` is complete if decrypting an encrypted message always returns that original
message, captured here by a `guard` statement. -/
class Complete (encAlg : SymmEncAlg spec em M K C) : Prop where
  decrypt_encrypt_eq_message (m : M) : [⊥ | encAlg.exec
    do let k ← encAlg.keygen; guard (encAlg.decrypt k (← encAlg.encrypt k m) = m)] = 0

lemma Complete_def (encAlg : SymmEncAlg spec em M K C) : encAlg.Complete ↔ ∀ m, [⊥ | encAlg.exec
    do let k ← encAlg.keygen; guard (encAlg.decrypt k (← encAlg.encrypt k m) = m)] = 0 :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

end sound

section perfectSecrecy

open ENNReal

def perfectSecrecy (encAlg : SymmEncAlg spec em M K C) : Prop :=
  ∀ message_dist : OracleComp spec M, ∀ m : M, ∀ σ : C,
    [= (m, σ) | encAlg.exec do
      let m' ← message_dist; (m', ·) <$> encAlg.encrypt (← encAlg.keygen) m'] =
    [= m | encAlg.exec message_dist]

-- /-- Shanon's theorem on perfect secrecy, showing that encryption and decryption must be non-probabalistic
-- bijections between message and cipher-text space, and that keys must be chosen uniformly at random. -/
-- theorem perfectSecrecy_iff_of_card_eq [Fintype M] [Fintype K] [Fintype C]
--     (encAlg : SymmEncAlg spec em M K C)
--     (h1 : Fintype.card M = Fintype.card K) (h2 : Fintype.card K = Fintype.card C) :
--     encAlg.perfectSecrecy ↔ (∀ k, [= k | encAlg.exec encAlg.keygen] = (Fintype.card K : ℝ≥0∞)⁻¹) ∧
--     (∀ m c, ∃! k, k ∈ (encAlg.keygen ()).support ∧ se_alg.encrypt (m, k) = c)

end perfectSecrecy

end SymmEncAlg
