/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp

/-!
# Sigma Protocol

This file defines a structure type for identification protocols.
-/

open OracleSpec OracleComp ENNReal

/-- A sigma protocol for statements in `X`, witnesses in `W`,
prover messages in `M`, verifier challenges in `C`,
and proofs in `P`.
`p` is the relation on statements and witnesses to be proven.

We leave properties like special soundness as seperate definitions for better modularity.-/
structure SigmaAlg {ι : Type} (spec : ℕ → OracleSpec ι)
    (X W C Γ Ω P : ℕ → Type) (r : (sp : ℕ) → X sp → W sp → Prop)
    extends OracleAlg spec where
  commit (sp : ℕ) : X sp → W sp → OracleComp (spec sp) (C sp × Γ sp)
  prove (sp : ℕ) : X sp → W sp → C sp → Γ sp → Ω sp → OracleComp (spec sp) (P sp)
  verify (sp : ℕ) : X sp → C sp → Ω sp → P sp → OracleComp (spec sp) Bool
  sim (sp : ℕ) : X sp → OracleComp (spec sp) (C sp)
  extract (sp : ℕ) : P sp → P sp → OracleComp (spec sp) (W sp)
