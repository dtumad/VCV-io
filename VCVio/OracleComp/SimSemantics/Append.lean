/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Simulate
import VCVio.OracleComp.OracleSpec.Append

/-!
# Append Operation for Simulation Oracles

This file defines a number of basic simulation oracles, as well as operations to combine them.
-/

open OracleSpec OracleComp Prod Sum

namespace SimOracle

section append

variable {spec₁ spec₂ specₜ : OracleSpec} {σ τ : Type}

/-- Given simulation oracles `so` and `so'` with source oracles `spec₁` and `spec₂` respectively,
with the same target oracles `specₜ`, construct a new simulation oracle from `specₜ`,
answering queries to either oracle set with queries to the corresponding simulation oracle. -/
def append (so : spec₁ →[σ]ₛₒ specₜ) (so' : spec₂ →[τ]ₛₒ specₜ) :
    spec₁ ++ spec₂ →[σ × τ]ₛₒ specₜ :=
  λ i ↦ match i with
  | (inl i) => λ ⟨t, s₁, s₂⟩ ↦ do
      let ⟨u, s₁'⟩ ← so i (t, s₁) return (u, s₁', s₂)
  | (inr i) => λ ⟨t, s₁, s₂⟩ ↦ do
      let ⟨u, s₂'⟩ ← so' i (t, s₂) return (u, s₁, s₂')

infixl : 65 " ++ₛₒ " => append

@[simp]
lemma append_apply_inl (so : spec₁ →[σ]ₛₒ specₜ) (so' : spec₂ →[τ]ₛₒ specₜ)
    (i : spec₁.ι) : (so ++ₛₒ so') (inl i) = λ ⟨t, s₁, s₂⟩ ↦ do
      let ⟨u, s₁'⟩ ← so i (t, s₁) return (u, s₁', s₂) := rfl

@[simp]
lemma append_apply_inr (so : spec₁ →[σ]ₛₒ specₜ) (so' : spec₂ →[τ]ₛₒ specₜ)
    (i : spec₂.ι) : (so ++ₛₒ so') (inr i) = λ ⟨t, s₁, s₂⟩ ↦ do
      let ⟨u, s₂'⟩ ← so' i (t, s₂) return (u, s₁, s₂') := rfl

end append
