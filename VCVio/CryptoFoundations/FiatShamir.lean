/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SigmaAlg
import VCVio.CryptoFoundations.SignatureAlg
import VCVio.OracleComp.SimSemantics.QueryTracking.RandOracle
import VCVio.OracleComp.Coercions.Append

/-!
# Fiat-Shamir Transform

This file defines a basic version of the Fiat-Shamir transform on sigma protocols.
For simplicity we construct signature schemes rather than general proofs of knowledge.
-/

-- TODO
open OracleComp OracleSpec

variable {ι : Type} (spec : ℕ → OracleSpec ι)
    (X W : ℕ → Type) (p : {n : ℕ} → X n → W n → Bool)
    (PC SC Ω P : ℕ → Type)
    [Π n, Inhabited (Ω n)]
    [Π n, DecidableEq (PC n)]
    [Π n, DecidableEq (Ω n)]
    [Π n, Fintype (Ω n)]
    [Π n, SelectableType (Ω n)]

/-- Given a Σ-protocol we get a signature algorithm by using a random oracle to generate
challenge values for the Σ-protocol, including the message in the hash input.

TODO: this suggests that we should maybe "auto-include" `unifSpec` in algorithms. -/
def FiatShamir (M : ℕ → Type) (sigmaAlg : SigmaAlg (λ n ↦ spec n) X W p PC SC Ω P)
    [Π n, DecidableEq (M n)] (hr : GenerableRelation spec X W p) :
    SignatureAlg (λ n ↦ spec n ++ₒ (M n × PC n →ₒ Ω n))
      (M := M) (PK := X) (SK := W)
      (S := λ n ↦ PC n × P n) where
  -- Use the existing algorithm for generating relation members
  keygen := λ n ↦ ↑(hr.gen n)
  -- Sign by running the sigma protocol using a hash as the challenge
  sign := λ n pk sk m ↦ sorry --do
    -- let (c, e) ← sigmaAlg.commit n pk sk
    -- let r ← query (Sum.inr ()) (m, c)
    -- let s ← sigmaAlg.respond n pk sk e r
    -- return (c, s)
  -- Verify a signature by checking the challenge returned by the random oracle
  verify := λ n pk m (c, s) ↦ sorry --do
    -- let r' ← query (Sum.inr ()) (m, c)
    -- return sigmaAlg.verify n pk c r' s
  -- Simulation includes an additional cache for random oracle
  baseState := λ n ↦ sigmaAlg.baseState n × QueryCache _
  -- Add an empty cache to initial state
  init_state := λ n ↦ (sigmaAlg.init_state n, ∅)
  -- Simulate the additional oracle as a random oracle
  baseSimOracle := λ n ↦ sigmaAlg.baseSimOracle n ++ₛₒ randOracle

namespace FiatShamir

-- TODO

end FiatShamir
