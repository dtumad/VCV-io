/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.UniformSelect
import VCVio.OracleComp.Coercions.SubSpec

/-!
# Asymmetric Encryption Schemes.

This file defines a type `AsymmEncAlg spec M PK SK C` to represent an protocol
for asymmetric encryption using oracles in `spec`, with message space `M`,
public/secret keys `PK` and `SK`, and ciphertext space `C`.
-/

open OracleSpec OracleComp

universe u v w

structure AsymmEncAlg {ι : Type} (spec : OracleSpec ι) (em : Type → Type v)
    (M PK SK C : Type) extends ExecutionMethod spec em where
  keygen : OracleComp spec (PK × SK)
  encrypt (m : M) (pk : PK) : OracleComp spec C
  decrypt (c : C) (sk : SK) : OracleComp spec M

namespace AsymmEncAlg

variable {ι : Type} {spec : OracleSpec ι} {M PK SK C : Type}
    {em : Type → Type v} [AlternativeMonad em] [LawfulAlternative em]

section sound

-- variable [Π sp, DecidableEq (M sp)]


-- /-- Experiment for checking that an asymmetric encryption algorithm is sound,
-- i.e. that decryption properly reverses encryption -/
-- def soundnessExp (encAlg : AsymmEncAlg spec M PK SK C)
--     (mDist : (sp : ℕ) → OracleComp (spec sp) (M sp)) :
--     SecExp spec where
--   main := λ sp ↦ do
--     let m ← mDist sp
--     let (pk, sk) ← encAlg.keygen sp
--     let σ ← encAlg.encrypt sp m pk
--     let m' ← encAlg.decrypt sp σ sk
--     return m = m'
--   __ := encAlg

def soundnessExp [DecidableEq M] (encAlg : AsymmEncAlg spec em M PK SK C)
    (m : M) : SecExp spec em where
  main := do
    let (pk, sk) ← encAlg.keygen
    let σ ← encAlg.encrypt m pk
    let m' ← encAlg.decrypt σ sk
    guard (m' = m)
  __ := encAlg

-- def IsSound [DecidableEq M] (encAlg : AsymmEncAlg spec em M PK SK C) : Prop :=
--   ∀ m : M, (soundnessExp encAlg m).advantage = 1

def IsSound [DecidableEq M] (encAlg : AsymmEncAlg spec em M PK SK C) : Prop :=
    ∀ m : M, [⊥ | encAlg.exec do
      let (pk, sk) ← encAlg.keygen
      let σ ← encAlg.encrypt m pk
      let m' ← encAlg.decrypt σ sk
      guard (m' = m)] = 0


-- namespace soundnessExp


-- end soundnessExp

-- /-- An asymmetric encryption algorithm is sound if messages always decrypt to themselves. -/
-- def isSound (encAlg : AsymmEncAlg spec M PK SK C) : Prop :=
--   ∀ mDist, negligible (1 - (soundnessExp encAlg mDist).advantage)

-- -- lemma sound_iff [DecidableEq M] (encAlg : AsymmEncAlg spec M PK SK C) : encAlg.isSound ↔
-- --     ∀ m : M, ∀ m' ∈ (encAlg.exec <| do
-- --       let (pk, sk) ← encAlg.keygen ()
-- --       let σ ← encAlg.encrypt m pk
-- --       encAlg.decrypt σ sk).support, m = m' := by
-- --   simp only [isSound, SecExp.advantage_eq_one_iff]
-- --   sorry

end sound

section IND_CPA

-- variable [DecidableEq ι]

variable [DecidableEq ι]

/-- `IND_CPA_adv M PK C` is an adversary for IND-CPA security game on an
asymmetric encryption with public keys in `PK`, messages in `M`, and ciphertexts in `C`.
Adversary is given a public key and returns a pair of messages that it thinks
it can distinguish the encryption of. It addionally has a `distinguish` function
that given a pair of messages and an encryption, returns whether it is an encryption of
the first message or the second message.
TODO: should use sim oracles to allow state sharing -/
structure IND_CPA_Adv (encAlg : AsymmEncAlg spec em M PK SK C)
    extends SecAdv spec PK (M × M) where
  distinguish : PK → M × M → C → OracleComp spec Bool

/-- Experiment for IND-CPA security of an asymmetric encryption algorithm.
`inp_gen` generates a key and pre-selects a random boolean value.
`main` runs the adversary on the public key, and encrypts the resulting message corresponding to
the boolean chosen in `inp_gen`, finally asking the adversary to determine the boolean
given the messages and resulting ciphertext. `is_valid` checks that this choice is correct.
The simulation oracles are pulled in directly from the encryption algorithm. -/
def IND_CPA_Exp [unifSpec ⊂ₒ spec]
    {encAlg : AsymmEncAlg spec em M PK SK C}
    (adv : IND_CPA_Adv encAlg) :
    SecExp spec em where
  main := do
    let (pk, _) ← encAlg.keygen
    let (m₁, m₂) ← adv.run pk
    let b : Bool ←$ᵗ Bool
    let m := if b then m₁ else m₂
    let c ← encAlg.encrypt m pk
    let b' ← adv.distinguish pk (m₁, m₂) c
    guard (b = b')
  __ := encAlg

end IND_CPA

end AsymmEncAlg
