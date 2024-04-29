/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.UniformSelect
import VCVio.OracleComp.OracleSpec.SubSpec

/-!
# Asymmetric Encryption Schemes.

This file defines a type `AsymmEncAlg spec M PK SK C` to represent an protocol
for asymmetric encryption using oracles in `spec`, with message space `M`,
public/secret keys `PK` and `SK`, and ciphertext space `C`.
-/

open OracleSpec OracleComp

structure AsymmEncAlg (spec : OracleSpec) (M PK SK C : Type)
    extends OracleAlg spec where
  keygen : Unit → OracleComp spec (PK × SK)
  encrypt : M → PK → OracleComp spec C
  decrypt : C → SK → OracleComp spec M

namespace AsymmEncAlg

variable {spec : OracleSpec} {M PK SK C : Type}

/-- Experiment for checking that an asymmetric encryption algorithm is sound,
i.e. that decryption properly reverses encryption -/
def soundnessExp [DecidableEq M] (encAlg : AsymmEncAlg spec M PK SK C)
    (m : M) : SecExp spec (PK × SK) where
  inpGen := encAlg.keygen ()
  main := λ (pk, sk) ↦ do
    let σ ← encAlg.encrypt m pk
    let m' ← encAlg.decrypt σ sk
    return m = m'
  __ := encAlg

namespace soundnessExp


end soundnessExp

/-- An asymmetric encryption algorithm is sound if messages always decrypt to themselves. -/
def sound [DecidableEq M] (encAlg : AsymmEncAlg spec M PK SK C) : Prop :=
  ∀ m : M, (soundnessExp encAlg m).advantage = 1

lemma sound_iff [DecidableEq M] (encAlg : AsymmEncAlg spec M PK SK C) : encAlg.sound ↔
    ∀ m m' : M, ∀ pk : PK, ∀ sk : SK, ∀ σ : C, ∀ s₁ s₂ s₃,
    ((pk, sk), s₁) ∈ (simulate encAlg.baseSimOracle encAlg.init_state (encAlg.keygen ())).support →
    (σ, s₂) ∈ (simulate encAlg.baseSimOracle s₁ (encAlg.encrypt m pk)).support →
    (m', s₃) ∈ (simulate encAlg.baseSimOracle s₂ (encAlg.decrypt σ sk)).support → m = m' := by
  simp [sound, soundnessExp]
  sorry

section IND_CPA

/-- `IND_CPA_adv M PK C` is an adversary for IND-CPA security game on an
asymmetric encryption algorithm with public keys in `PK`, messages in `M`, and ciphertexts in `C`.
Adversary is given a public key and returns a pair of messages that it thinks
it can distinguish the encryption of. It addionally has a `distinguish` function
that given a pair of messages and an encryption, returns whether it is an encryption of
the first message or the second message. -/
structure IND_CPA_Adv (encAlg : AsymmEncAlg spec M PK SK C)
    extends SecAdv spec PK (M × M) where
  distinguish : PK → M × M → C → OracleComp spec Bool
  -- (distinguish_qb : query_count spec)

/-- Experiment for IND-CPA security of an asymmetric encryption algorithm.
`inp_gen` generates a key and pre-selects a random boolean value.
`main` runs the adversary on the public key, and encrypts the resulting message corresponding to
the boolean chosen in `inp_gen`, finally asking the adversary to determine the boolean
given the messages and resulting ciphertext. `is_valid` checks that this choice is correct.
The simulation oracles are pulled in directly from the encryption algorithm. -/
def IND_CPA_Exp [coinSpec ⊂ₒ spec] (encAlg : AsymmEncAlg spec M PK SK C)
    (adv : IND_CPA_Adv encAlg) : SecExp spec (PK × Bool) where
  inpGen := do
    let ⟨pk, _⟩ ← encAlg.keygen ()
    let b ← ↑coin
    return (pk, b)
  main := λ ⟨pk, b⟩ ↦ do
    let ⟨m₁, m₂⟩ ← adv.run pk
    let m := if b then m₁ else m₂
    let c ← encAlg.encrypt m pk
    let b' ← adv.distinguish pk (m₁, m₂) c
    return b = b'
  __ := encAlg

end IND_CPA

end AsymmEncAlg
