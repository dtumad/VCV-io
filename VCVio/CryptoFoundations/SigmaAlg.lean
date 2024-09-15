/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation

/-!
# Sigma Protocol

This file defines a structure type for Σ-protocols.
-/

open OracleSpec OracleComp

/-- A sigma protocol for statements in `X`, witnesses in `W`,
where `p` is the proposition that is proven by the Σ-protocol.

commitments in `PC`/`SC`, verifier challenges in `Ω`,
and responses in `P`. `r` is the relation on statements and witnesses to be proven.

We have two types for the commitments in order to allow for a public part in `PC`
and secret part in `SC`. Only the commitment in `PC` is revealed to the verifier,
but the `prove` function may still use `SC` in generating a proof.

We leave properties like special soundness as seperate definitions for better modularity.-/
structure SigmaAlg {ι : Type} (spec : ℕ → OracleSpec ι)
    (X W : ℕ → Type) (p : {n : ℕ} → X n → W n → Bool)
    (PC SC Ω P : ℕ → Type) extends OracleAlg spec where
  commit (n : ℕ) : X n → W n → OracleComp (unifSpec ++ₒ spec n) (PC n × SC n)
  respond (n : ℕ) : X n → W n → SC n → Ω n → OracleComp (unifSpec ++ₒ spec n) (P n)
  verify (n : ℕ) : X n → PC n → Ω n → P n → Bool
  sim (n : ℕ) : X n → OracleComp (unifSpec ++ₒ spec n) (PC n)
  extract (n : ℕ) : Ω n → P n → Ω n → P n → OracleComp (unifSpec ++ₒ spec n) (W n)

namespace SigmaAlg

section complete

-- TODO

end complete

section speciallySound

-- TODO

end speciallySound

end SigmaAlg
