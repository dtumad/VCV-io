/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.UniformSelect
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.QueryTracking.CachingOracle

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

variable [DecidableEq M] [AlternativeMonad m]

/-- A `SymmEncAlg` is complete if decrypting an encrypted message always returns that original
message, captured here by a `guard` statement. -/
@[reducible, inline]
def CorrectExp (encAlg : AsymmEncAlg m M PK SK C) (msg : M) :
    ProbComp Unit := encAlg.exec do
  let (pk, sk) ← encAlg.keygen
  guard (encAlg.decrypt sk (← encAlg.encrypt pk msg) = msg)

def PerfectlyCorrect (encAlg : AsymmEncAlg m M PK SK C) : Prop :=
  ∀ (msg : M), [⊥ | CorrectExp encAlg msg] = 0

@[simp] lemma PerfectlyCorrect_iff (encAlg : AsymmEncAlg m M PK SK C) :
    PerfectlyCorrect encAlg ↔ ∀ (msg : M),
      [⊥ | CorrectExp encAlg msg] = 0 := Iff.rfl

end Correct

section IND_CPA

variable [DecidableEq M] [DecidableEq C]

-- Simplifying assumption: The algorithm is defined over `ProbComp`

def IND_CPA_oracleSpec (_encAlg : AsymmEncAlg ProbComp M PK SK C) :=
  unifSpec ++ₒ (M × M →ₒ C) -- Second oracle for adversary to request challenge

def IND_CPA_adversary (encAlg : AsymmEncAlg ProbComp M PK SK C) :=
  PK → OracleComp encAlg.IND_CPA_oracleSpec Bool
  -- with poly functors: `ProbComp ((M × M) × (C → ProbComp Bool))`

/-- Can be shown this is equivalent to below definition for asymptotic security. -/
def IND_CPA_queryImpl' (encAlg : AsymmEncAlg ProbComp M PK SK C)
    (pk : PK) (b : Bool) : QueryImpl encAlg.IND_CPA_oracleSpec
      (StateT (M × M →ₒ C).QueryCache ProbComp) :=
  have so : QueryImpl (M × M →ₒ C) ProbComp := ⟨fun (query () (m₁, m₂)) =>
    encAlg.encrypt pk (if b then m₁ else m₂)⟩
  idOracle ++ₛₒ so.withCaching

def IND_CPA_queryImpl (encAlg : AsymmEncAlg ProbComp M PK SK C)
    (pk : PK) (b : Bool) : QueryImpl encAlg.IND_CPA_oracleSpec
      (StateT (M × M →ₒ C).QueryCache ProbComp) :=
  have so : QueryImpl (M × M →ₒ C) ProbComp := ⟨fun (query () (m₁, m₂)) =>
    encAlg.encrypt pk (if b then m₁ else m₂)⟩
  idOracle ++ₛₒ so

def IND_CPA_experiment {encAlg : AsymmEncAlg ProbComp M PK SK C}
    (adversary : encAlg.IND_CPA_adversary) : ProbComp Unit := do
  let b ← $ᵗ Bool
  let (pk, _sk) ← encAlg.keygen
  let b' ← (simulateQ (encAlg.IND_CPA_queryImpl' pk b) (adversary pk)).run' ∅
  guard (b = b')

noncomputable def IND_CPA_advantage {encAlg : AsymmEncAlg ProbComp M PK SK C}
    (adversary : encAlg.IND_CPA_adversary) : ℝ≥0∞ :=
  [= () | IND_CPA_experiment adversary] - 1 / 2

lemma probOutput_IND_CPA_experiment_eq_add {encAlg : AsymmEncAlg ProbComp M PK SK C}
    (adversary : encAlg.IND_CPA_adversary) :
    [= () | IND_CPA_experiment adversary] =
      [= () | do
        let (pk, _sk) ← encAlg.keygen
        let b ← (simulateQ (encAlg.IND_CPA_queryImpl' pk true) (adversary pk)).run' ∅
        guard b] / 2 +
      [= () | do
        let (pk, _sk) ← encAlg.keygen
        let b ← (simulateQ (encAlg.IND_CPA_queryImpl' pk false) (adversary pk)).run' ∅
        guard ¬b] / 2 :=
  sorry

end IND_CPA

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

end AsymmEncAlg
