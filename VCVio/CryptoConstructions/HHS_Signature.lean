/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.HardnessAssumptions.HardHomogeneousSpace
import VCVio.CryptoFoundations.SignatureAlg
import Mathlib.Data.Vector.Zip
import VCVio.OracleComp.Constructions.Replicate

/-!
# HHS Based Schnorr Signature
-/

open OracleSpec OracleComp Sum

-- TODO: This is needed for computability but we need a better interface
instance (G P M : Type) [DecidableEq M]
    [AddCommGroup G] [HomogeneousSpace G P] (n : ℕ) : ∀ i, SelectableType
  <| ((((Vector P n × M) →ₒ Vector Bool n))).range i := sorry

section commits

variables {G P M : Type} [DecidableEq M]
    [AddCommGroup G] [HomogeneousSpace G P]

def zipCommits (sk : G) (gs : Vector G n)
    (bs : Vector Bool n) : Vector G n :=
  Vector.zipWith (λ c b ↦
    if b then c else c + sk) gs bs

def unzipCommits (x₀ pk : P) (zs : Vector G n)
    (hash : Vector Bool n) : Vector P n :=
  Vector.zipWith (λ z b ↦
    if b then z +ᵥ pk else z +ᵥ x₀) zs hash


end commits

def HHS_signature (G P M : Type) [DecidableEq M]
    [AddCommGroup G] [HomogeneousSpace G P] (n : ℕ) :
    SignatureAlg (unifSpec ++ ((Vector P n × M) →ₒ Vector Bool n))
      M (P × P) G (Vector G n × Vector Bool n) where
  keygen := λ () ↦ do
    let x₀ ← $ᵗ P; let sk ← $ᵗ G
    return ((x₀, sk +ᵥ x₀), sk)
  -- Sign a message by choosing `n` random commitments, and querying the oracle on them
  -- For each 1 bit in the resulting hash, subtract the secret key from corresponding commitment
  sign := λ (_, pk) sk m ↦ do
    let gs : Vector G n ← replicate ($ᵗ G) n
    let xs : Vector P n := gs.map (· +ᵥ pk)
    let j : (unifSpec ++ ((Vector P n × M) →ₒ Vector Bool n)).ι := inr ()
    let bs : Vector Bool n ← query j (xs, m)
    let zs : Vector G n := zipCommits sk gs bs
    return (zs, bs)
  -- Verify a signature by adding each commit to the appropriate point in the public key
  -- Signatures are valid if the result of hashing this matches the original hash
  verify := λ ⟨x₀, pk⟩ m (zs, bs) ↦ do
    let xs : Vector P n := unzipCommits x₀ pk zs bs
    let j : (unifSpec ++ ((Vector P n × M) →ₒ Vector Bool n)).ι := inr ()
    let bs' : Vector Bool n ← query j (xs, m)
    return (bs' = bs)
  -- Treat the second oracle as a random oracle
  baseSimOracle := SimOracle.maskState
    (idOracle ++ₛₒ randOracle) (Equiv.punitProd _)
  init_state := ∅
