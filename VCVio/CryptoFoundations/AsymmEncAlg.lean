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

/-- An `AsymmEncAlg` with message space `M`, key spaces `PK` and `SK`, and ciphertexts in `C`.
`spec` is the available oracle set and `m` is the monad used to execute the oracle calls.
Extends `ExecutionMethod spec m`, in most cases will be `ExecutionMethod.default`. -/
structure AsymmEncAlg (m : Type → Type u) (M PK SK C : Type)
    extends ExecutionMethod m where
  keygen : m (PK × SK)
  encrypt : (pk : PK) → (msg : M) →  m C
  decrypt : (sk : SK) → (c : C) → Option M

alias PKE_Alg := AsymmEncAlg

namespace AsymmEncAlg

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type v} {M PK SK C : Type}
  (encAlg : AsymmEncAlg m M PK SK C) {α β γ : Type}

section Correct

-- variable [AlternativeMonad m] [LawfulAlternative m] [DecidableEq M]
variable [DecidableEq M] [AlternativeMonad m]

/-- A `SymmEncAlg` is complete if decrypting an encrypted message always returns that original
message, captured here by a `guard` statement. -/
@[reducible, inline]
-- def CorrectExp (encAlg : AsymmEncAlg spec m M PK SK C) (msg : M) :
--     ProbComp Unit := encAlg.exec do
--   let (pk, sk) ← encAlg.keygen
--   guard (encAlg.decrypt sk (← encAlg.encrypt pk msg) = msg)

def CorrectExp (encAlg : AsymmEncAlg m M PK SK C) (msg : M) :
    ProbComp Unit := encAlg.exec do
  let (pk, sk) ← encAlg.keygen
  guard (encAlg.decrypt sk (← encAlg.encrypt pk msg) = msg)

/-- Perfectly correct if messages never fail to decrypt back to themselves for any message. -/
-- def PerfectlyCorrect (encAlg : AsymmEncAlg spec m M PK SK C) : Prop :=
--   ∀ (msg : M), [⊥ | CorrectExp encAlg msg] = 0

def PerfectlyCorrect (encAlg : AsymmEncAlg m M PK SK C) : Prop :=
  ∀ (msg : M), [⊥ | CorrectExp encAlg msg] = 0

-- @[simp] lemma PerfectlyCorrect_iff : encAlg.PerfectlyCorrect ↔
--     ∀ (msg : M), [⊥ | CorrectExp encAlg msg] = 0 := Iff.rfl

@[simp] lemma PerfectlyCorrect_iff (encAlg : AsymmEncAlg m M PK SK C) :
    PerfectlyCorrect encAlg ↔
    ∀ (msg : M), [⊥ | CorrectExp encAlg msg] = 0 := Iff.rfl

end Correct

section decryptionOracle

variable [AlternativeMonad m]

/-- Oracle that uses a secret key to respond to decryption requests. -/
def decryptionOracle (encAlg : AsymmEncAlg m M PK SK C)
    (sk : SK) : QueryImpl (C →ₒ M) m where
  impl | query () c => Option.getM (encAlg.decrypt sk c)

@[simp]
lemma decryptionOracle.apply_eq (encAlg : AsymmEncAlg m M PK SK C)
    (sk : SK) (q : OracleQuery (C →ₒ M) α) : (decryptionOracle encAlg sk).impl q =
    match q with | query () c => Option.getM (encAlg.decrypt sk c) := rfl

end decryptionOracle

section IND_CCA

variable [AlternativeMonad m] [LawfulAlternative m] [DecidableEq C]

/-- Two oracles for IND-CCA Experiment, the first for decrypting ciphertexts, and the second
for getting a challenge from a pair of messages. -/
def IND_CCA_oracleSpec (_encAlg : AsymmEncAlg m M PK SK C) :=
    (C →ₒ Option M) ++ₒ ((M × M) →ₒ C)

/-- Implement oracles for IND-CCA security game. A state monad is to track the current challenge,
if it exists, and is set by the adversary calling the second oracle.
The decryption oracle checks to make sure it doesn't decrypt the challenge. -/
def IND_CCA_oracleImpl [DecidableEq C] (encAlg : AsymmEncAlg m M PK SK C)
    (pk : PK) (sk : SK) (b : Bool) : QueryImpl (IND_CCA_oracleSpec encAlg)
      (StateT (Option C) m) where impl
  | query (Sum.inl ()) c => do
      guard ((← get) ≠ some c)
      return encAlg.decrypt sk c
  | query (Sum.inr ()) (m₁, m₂) => do
      guard (← get).isNone
      let c ← encAlg.encrypt pk (if b then m₁ else m₂)
      set (some c)
      return c

structure IND_CCA_Adversary (encAlg : AsymmEncAlg m M PK SK C) where
    main : PK → OracleComp encAlg.IND_CCA_oracleSpec Bool

def IND_CCA_Game (encAlg : AsymmEncAlg m M PK SK C)
    (adversary : encAlg.IND_CCA_Adversary) : ProbComp Unit :=
  encAlg.exec do
    let (pk, sk) ← encAlg.keygen
    let b ← encAlg.lift_probComp ($ᵗ Bool)
    let b' ← (simulateQ (encAlg.IND_CCA_oracleImpl pk sk b) (adversary.main pk)).run' none
    guard (b = b')

end IND_CCA

section IND_CPA

variable [DecidableEq ι]

variable [AlternativeMonad m] [LawfulAlternative m] [DecidableEq ι]

-- /-- `IND_CPA_adv M PK C` is an adversary for IND-CPA security game on an
-- asymmetric encryption with public keys in `PK`, messages in `M`, and ciphertexts in `C`.
-- Adversary is given a public key and returns a pair of messages that it thinks
-- it can distinguish the encryption of. It addionally has a `distinguish` function
-- that given a pair of messages and an encryption, returns whether it is an encryption of
-- the first message or the second message.
-- TODO: should use sim oracles to allow state sharing -/
structure IND_CPA_Adv (encAlg : AsymmEncAlg m M PK SK C)
    extends SecAdv spec PK (M × M) where
  distinguish : PK → M × M → C → m Bool

variable {encAlg : AsymmEncAlg (OracleComp spec) M PK SK C}
  (adv : IND_CPA_Adv (spec := spec) encAlg)

-- /-- Experiment for IND-CPA security of an asymmetric encryption algorithm.
-- `inp_gen` generates a key and pre-selects a random boolean value.
-- `main` runs the adversary on the public key, and encrypts the resulting message corresponding to
-- the boolean chosen in `inp_gen`, finally asking the adversary to determine the boolean
-- given the messages and resulting ciphertext. `is_valid` checks that this choice is correct.
-- The simulation oracles are pulled in directly from the encryption algorithm. -/
def IND_CPA_Exp : ProbComp Unit :=
  encAlg.exec do
    let (pk, _) ← encAlg.keygen
    let (m₁, m₂) ← adv.run pk
    let b : Bool ← encAlg.lift_probComp ($ᵗ Bool)
    let m := if b then m₁ else m₂
    let c ← encAlg.encrypt pk m
    let b' ← adv.distinguish pk (m₁, m₂) c
    guard (b = b')

noncomputable def IND_CPA_Advantage : ℝ := abs (1 / 2 - ([⊥ | IND_CPA_Exp adv]).toReal)

--   -- main := do
--   --   let (pk, _) ← encAlg.keygen
--   --   let (m₁, m₂) ← adv.run pk
--   --   let b : Bool ←$ᵗ Bool
--   --   let m := if b then m₁ else m₂
--   --   let c ← encAlg.encrypt pk m
--   --   let b' ← adv.distinguish pk (m₁, m₂) c
--   --   guard (b = b')
--   -- __ := encAlg

-- def IND_CPA_Security {encAlg : AsymmEncAlg (OracleComp spec) M PK SK C} :=
--   ∀ (adv : IND_CPA_Adv encAlg),

end IND_CPA

-- Define LWE

-- (A, As + e) ≈ (A, u)

variable {m n p χ : ℕ} (adv : Matrix (Fin m) (Fin n) (Fin p) × Vector (Fin p) n → ProbComp Bool)

def LWE_Exp : ProbComp Unit := do
    let A ←$ᵗ Matrix (Fin m) (Fin n) (Fin p)
    let s ←$ᵗ Vector (Fin p) m
    let e ←$ᵗ Vector (Fin p) m
    let u ←$ᵗ Vector (Fin p) n
    let b ←$ᵗ Bool
    let dist := if b then (A, (A.vecMul s.get) + e) else (A, u)
    let b' ← adv dist
    guard (b = b')

noncomputable def LWE_Advantage : ℝ := abs (1 / 2 - ([⊥ | LWE_Exp adv]).toReal)

variable [DecidableEq ι]

-- Original hybrid (hybrid 0) is the IND-CPA experiment

-- Want to show:
-- ∀ adv in hybrid 0,
  -- advantage (hybrid 0, adv) ≤ advantage (hybrid 1, reduction1 (adv)) + advantage (LWE game, ...)
-- ∀ adv in hybrid 1, advantage (hybrid 1, adv) ≤ advantage (hybrid 2, reduction2 (adv))

def Regev_Hybrid_1 : ProbComp Unit := do sorry
    -- let A ←$ᵗ Matrix (Fin m) (Fin n) (Fin p)
    -- let s ←$ᵗ Vector (Fin p) m
    -- let e ←$ᵗ Vector (Fin p) m
    -- let u ←$ᵗ Vector (Fin p) n
    -- let b ←$ᵗ Bool
    -- let dist := if b then (A, (A.vecMul s.get) + e) else (A, u)

def Regev_Hybrid_2 : ProbComp Unit := do sorry

theorem Regev_IND_CPA {encAlg : AsymmEncAlg (OracleComp spec) M PK SK C}
    {adv : IND_CPA_Adv (spec := spec) encAlg} :
    IND_CPA_Advantage adv ≤ LWE_Advantage adv := by

end AsymmEncAlg
