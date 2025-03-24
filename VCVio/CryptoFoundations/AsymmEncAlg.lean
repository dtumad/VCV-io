/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.UniformSelect
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.SimSemantics.Append

/-!
# Asymmetric Encryption Schemes.

This file defines a type `AsymmEncAlg spec M PK SK C` to represent an protocol
for asymmetric encryption using oracles in `spec`, with message space `M`,
public/secret keys `PK` and `SK`, and ciphertext space `C`.
-/

open OracleSpec OracleComp ENNReal

universe u v w

def withRejection {ι : Type u} {spec : OracleSpec ι} {m : Type v → Type w} [Alternative m]
    (so : QueryImpl spec m) (prohibited : {i : ι} → spec.domain i → Prop)
    [∀ i, DecidablePred (@prohibited i)] :
    QueryImpl spec m where
  impl | query i t => if prohibited t then failure else so.impl (query i t)


/-- An `AsymmEncAlg` with message space `M`, key spaces `PK` and `SK`, and ciphertexts in `C`.
`spec` is the available oracle set and `m` is the monad used to execute the oracle calls.
Extends `ExecutionMethod spec m`, in most cases will be `ExecutionMethod.default`. -/
structure AsymmEncAlg {ι : Type} (spec : OracleSpec ι) (m : Type → Type v)
    (M PK SK C : Type) extends ExecutionMethod spec m where
  keygen : OracleComp spec (PK × SK)
  encrypt (pk : PK) (m : M) : OracleComp spec C
  decrypt (sk : SK) (c : C) : Option M

alias PKE_Alg := AsymmEncAlg

namespace AsymmEncAlg

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type v} {M PK SK C : Type}
  (encAlg : AsymmEncAlg spec m M PK SK C) {α β γ : Type}

section Correct

variable [AlternativeMonad m] [LawfulAlternative m] [DecidableEq M]

/-- A `SymmEncAlg` is complete if decrypting an encrypted message always returns that original
message, captured here by a `guard` statement. -/
@[reducible, inline]
def CorrectExp (encAlg : AsymmEncAlg spec m M PK SK C) (msg : M) :
    ProbComp Unit := encAlg.exec do
  let (pk, sk) ← encAlg.keygen
  guard (encAlg.decrypt sk (← encAlg.encrypt pk msg) = msg)

/-- Perfectly correct if messages never fail to decrypt back to themselves for any message. -/
def PerfectlyCorrect (encAlg : AsymmEncAlg spec m M PK SK C) : Prop :=
  ∀ (msg : M), [⊥ | CorrectExp encAlg msg] = 0

@[simp] lemma PerfectlyCorrect_iff : encAlg.PerfectlyCorrect ↔
    ∀ (msg : M), [⊥ | CorrectExp encAlg msg] = 0 := Iff.rfl

end Correct

/-- Oracle that uses a secret key to respond to decryption requests. -/
def decryptionOracle (encAlg : AsymmEncAlg spec m M PK SK C)
    (sk : SK) : QueryImpl (C →ₒ M) (OracleComp spec) where
  impl | query () c => Option.getM (encAlg.decrypt sk c)

@[simp]
lemma decryptionOracle.apply_eq (encAlg : AsymmEncAlg spec m M PK SK C)
    (sk : SK) (q : OracleQuery (C →ₒ M) α) : (decryptionOracle encAlg sk).impl q =
    match q with | query () c => Option.getM (encAlg.decrypt sk c) := rfl

section IND_CCA

variable [AlternativeMonad m] [LawfulAlternative m] [DecidableEq C]

/-- Two oracles for IND-CCA Experiment, the first for decrypting ciphertexts, and the second
for getting a challenge from a pair of messages. -/
def IND_CCA_oracleSpec (_encAlg : AsymmEncAlg spec m M PK SK C) :=
    (C →ₒ M) ++ₒ ((M × M) →ₒ C)

def IND_CCA_oracleImpl [DecidableEq C] (encAlg : AsymmEncAlg spec m M PK SK C)
    (pk : PK) (sk : SK) (b : Bool) : QueryImpl (IND_CCA_oracleSpec encAlg)
      (StateT (Option C) (OracleComp spec)) where impl
  | query (Sum.inl ()) c => do
      guard ((← get) ≠ some c)
      Option.getM (encAlg.decrypt sk c)
  | query (Sum.inr ()) (m₁, m₂) => do
      guard (← get).isNone
      let m := if b then m₁ else m₂
      let c ← encAlg.encrypt pk m
      set (some c)
      return c

structure IND_CCA_Adversary (encAlg : AsymmEncAlg spec m M PK SK C) where
    main : PK → OracleComp (encAlg.IND_CCA_oracleSpec) Bool

def IND_CCA_Game [coinSpec ⊂ₒ spec] (encAlg : AsymmEncAlg spec m M PK SK C)
    (adversary : encAlg.IND_CCA_Adversary) : ProbComp Unit := encAlg.exec do
  let (pk, sk) ← encAlg.keygen; let b ← coin
  let b' ← (simulateQ (encAlg.IND_CCA_oracleImpl pk sk b) (adversary.main pk)).run' none
  guard (b = b')

end IND_CCA

section IND_CPA

-- variable [DecidableEq ι]

variable [AlternativeMonad m] [LawfulAlternative m] [DecidableEq ι]

/-- `IND_CPA_adv M PK C` is an adversary for IND-CPA security game on an
asymmetric encryption with public keys in `PK`, messages in `M`, and ciphertexts in `C`.
Adversary is given a public key and returns a pair of messages that it thinks
it can distinguish the encryption of. It addionally has a `distinguish` function
that given a pair of messages and an encryption, returns whether it is an encryption of
the first message or the second message.
TODO: should use sim oracles to allow state sharing -/
structure IND_CPA_Adv (encAlg : AsymmEncAlg spec m M PK SK C)
    extends SecAdv spec PK (M × M) where
  distinguish : PK → M × M → C → OracleComp spec Bool

/-- Experiment for IND-CPA security of an asymmetric encryption algorithm.
`inp_gen` generates a key and pre-selects a random boolean value.
`main` runs the adversary on the public key, and encrypts the resulting message corresponding to
the boolean chosen in `inp_gen`, finally asking the adversary to determine the boolean
given the messages and resulting ciphertext. `is_valid` checks that this choice is correct.
The simulation oracles are pulled in directly from the encryption algorithm. -/
def IND_CPA_Exp [unifSpec ⊂ₒ spec]
    {encAlg : AsymmEncAlg spec m M PK SK C}
    (adv : IND_CPA_Adv encAlg) : ProbComp Unit :=
  encAlg.exec do
    let (pk, _) ← encAlg.keygen
    let (m₁, m₂) ← adv.run pk
    let b : Bool ←$ᵗ Bool
    let m := if b then m₁ else m₂
    let c ← encAlg.encrypt pk m
    let b' ← adv.distinguish pk (m₁, m₂) c
    guard (b = b')

  -- main := do
  --   let (pk, _) ← encAlg.keygen
  --   let (m₁, m₂) ← adv.run pk
  --   let b : Bool ←$ᵗ Bool
  --   let m := if b then m₁ else m₂
  --   let c ← encAlg.encrypt pk m
  --   let b' ← adv.distinguish pk (m₁, m₂) c
  --   guard (b = b')
  -- __ := encAlg

end IND_CPA

section IND_CCA



end IND_CCA

end AsymmEncAlg
