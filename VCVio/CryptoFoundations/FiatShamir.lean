/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SigmaAlg
import VCVio.CryptoFoundations.SignatureAlg
import VCVio.OracleComp.SimSemantics.QueryTracking.CachingOracle
import VCVio.OracleComp.Coercions.Append

/-!
# Fiat-Shamir Transform

This file defines a basic version of the Fiat-Shamir transform on sigma protocols.
For simplicity we construct signature schemes rather than general proofs of knowledge.
-/

-- TODO
open OracleComp OracleSpec

variable {ι : Type} (spec : ℕ → OracleSpec ι)
    (X W C E Ω P : ℕ → Type) (r : (sp : ℕ) → X sp → W sp → Prop)
    [Π sp, Inhabited (Ω sp)]
    [Π sp, DecidableEq (C sp)]

    [Π sp, DecidableEq (Ω sp)]
    [Π sp, Fintype (Ω sp)]
    [Π sp, SelectableType (Ω sp)]


def FiatShamir (M : ℕ → Type) [Π sp, DecidableEq (M sp)]
    (sigmaAlg : SigmaAlg spec X W C E Ω P r)
    (keygen : (sp : ℕ) → OracleComp (spec sp) (X sp × W sp)) :
    SignatureAlg (λ sp ↦ spec sp ++ₒ (M sp × C sp →ₒ Ω sp))
      (M := M) (PK := X) (SK := W)
      (S := λ sp ↦ C sp × P sp) where
  keygen := λ sp ↦ keygen sp
  sign := λ sp pk sk m ↦ do
    let (c, e) ← sigmaAlg.commit sp pk sk
    let r ← query (Sum.inr ()) (m, c)
    let s ← sigmaAlg.prove sp pk sk c e r
    return (c, s)
  verify := λ sp pk m (c, s) ↦ do
    let r' ← query (Sum.inr ()) (m, c)
    sigmaAlg.verify sp pk c r' s
  baseState := λ sp ↦ sigmaAlg.baseState sp × QueryCache _
  init_state := λ sp ↦ (sigmaAlg.init_state sp, ∅)
  baseSimOracle := λ sp ↦ sigmaAlg.baseSimOracle sp ++ₛₒ randOracle
