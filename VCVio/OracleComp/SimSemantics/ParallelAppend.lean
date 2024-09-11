/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coercions.Append
import VCVio.OracleComp.SimSemantics.Append

/-!
# (Modified) Append Operation for Simulation Oracles

This file experiments with an alternative version of `SimOracle.append`,
denoted with `||ₛₒ` instead of `++ₛₒ` that doesn't also appends the target specs.
This feels less general but might be useful so playing around with it.
-/

open OracleSpec OracleComp

namespace SimOracle

-- TODO: This should have its own place
instance  {ι ι' τ : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {source_spec : OracleSpec τ} {σ : Type}
    [∀ α, Coe (OracleComp spec α) (OracleComp spec' α)] :
    Coe (source_spec →[σ]ₛₒ spec) (source_spec →[σ]ₛₒ spec') where
  coe := λ so i t s ↦ ↑(so i t s)

def parallelAppend {ι₁ ι₂ ι₃ ι₄ : Type}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {spec₃ : OracleSpec ι₃} {spec₄ : OracleSpec ι₄} {σ τ : Type}
    (so : spec₁ →[σ]ₛₒ spec₂) (so' : spec₃ →[τ]ₛₒ spec₄) :
    spec₁ ++ₒ spec₃ →[σ × τ]ₛₒ spec₂ ++ₒ spec₄ :=
  ↑so ++ₛₒ ↑so'

infixl : 65 " ||ₛₒ " => parallelAppend

end SimOracle
