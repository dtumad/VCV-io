/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.SimSemantics.Append

/-!
# Coercing Oracle Outputs

This file defines a function `liftSO` for lifting a simulation oracle
given a lift from the original to final output oracle sets.
-/

open OracleSpec OracleComp

universe u v w

variable {ι ι₁ ι₂ : Type}
  {spec : OracleSpec ι} {spec₁ : OracleSpec ι₁}
  {spec₂ : OracleSpec ι₂} {σ α β γ : Type u}

namespace SimOracle

def liftSO [spec₁ ⊂ₒ spec₂] (so : SimOracle spec spec₁ σ) :
    SimOracle spec spec₂ σ := ⟨liftM ∘ so.impl⟩

@[simp]
lemma simulateT_liftSO_eq_liftM_simulateT [spec₁ ⊂ₒ spec₂] (so : SimOracle spec spec₁ σ)
    (oa : OracleComp spec α) :
    (simulateT (liftSO so) oa : StateT σ (OracleComp spec₂) α) =
      liftM (simulateT so oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp; rfl
  | query_bind i t oa h => sorry
  | failure => simp; rfl

example {ι₁ ι₁' ι₂ ι₂' σ τ : Type}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {specₜ₁ : OracleSpec ι₁'} {specₜ₂ : OracleSpec ι₂'}
    (so : SimOracle spec₁ specₜ₁ σ) (so' : SimOracle spec₂ specₜ₂ τ) :
    SimOracle (spec₁ ++ₒ spec₂) (specₜ₁ ++ₒ specₜ₂) (σ × τ) :=
  liftSO so ++ₛₒ liftSO so'

end SimOracle
