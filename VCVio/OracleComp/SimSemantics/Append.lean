/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Simulate

/-!
# Append Operation for Simulation Oracles

This file defines an operation `SimOracle.append` that takes two simulation oracles `so` and `so'`
from `spec₁` and `spec₂` respectively to a shared target spec `specₜ`,
and constructs a new simulation oracle from `spec₁ ++ spec₂` to `specₜ`.

This operation is also compatible with the `SubSpec` instances involving `OracleSpec.append`.
For example if `oa : OracleComp spec₁ α` is coerced to `↑oa : OracleComp (spec₁ ++ spec₂) α`,
then we have `simulate' (so ++ₛₒ so') ↑oa s = simulate' so oa s.1`, as the additional
oracles from the coercion will never actually be called.
-/

open OracleSpec OracleComp Prod Sum

namespace SimOracle

variable {ι₁ ι₂ ιₜ : Type} {spec₁ : OracleSpec ι₁}
  {spec₂ : OracleSpec ι₂} {specₜ : OracleSpec ιₜ} {σ τ α β : Type}

section append

/-- Given simulation oracles `so` and `so'` with source oracles `spec₁` and `spec₂` respectively,
with the same target oracles `specₜ`, construct a new simulation oracle from `specₜ`,
answering queries to either oracle set with queries to the corresponding simulation oracle. -/
def append (so : spec₁ →[σ]ₛₒ specₜ) (so' : spec₂ →[τ]ₛₒ specₜ) :
    spec₁ ++ₒ spec₂ →[σ × τ]ₛₒ specₜ :=
  λ i ↦ match i with
  | (inl i) => λ t (s₁, s₂) ↦ do
      let (u, s₁') ← so i t s₁ return (u, s₁', s₂)
  | (inr i) => λ t (s₁, s₂) ↦ do
      let (u, s₂') ← so' i t s₂ return (u, s₁, s₂')

infixl : 65 " ++ₛₒ " => append

@[simp]
lemma append_apply_inl (so : spec₁ →[σ]ₛₒ specₜ) (so' : spec₂ →[τ]ₛₒ specₜ)
    (i : ι₁) : (so ++ₛₒ so') (inl i) = λ t (s₁, s₂) ↦ do
      let (u, s₁') ← so i t s₁ return (u, s₁', s₂) := rfl

@[simp]
lemma append_apply_inr (so : spec₁ →[σ]ₛₒ specₜ) (so' : spec₂ →[τ]ₛₒ specₜ)
    (i : ι₂) : (so ++ₛₒ so') (inr i) = λ t (s₁, s₂) ↦ do
      let (u, s₂') ← so' i t s₂ return (u, s₁, s₂') := rfl

end append

section subSpec

-- @[simp]
-- lemma simulate_coe_append_left (so : spec₁ →[σ]ₛₒ specₜ) (so' : spec₂ →[τ]ₛₒ specₜ)
--     (oa : OracleComp spec₁ α) (s : σ × τ) :
--     simulate (so ++ₛₒ so') s ↑oa = (λ (x, s') ↦ (x, (s', s.2))) <$> simulate so s.1 oa := by
--   revert s; induction oa using OracleComp.inductionOn with
--   | h_pure x => simp
--   | h_queryBind i t oa hoa =>
--       simp only [subSpec_append_left_toFun] at hoa
--       simp [hoa, map_bind]

-- @[simp]
-- lemma simulate'_coe_append_left (so : spec₁ →[σ]ₛₒ specₜ) (so' : spec₂ →[τ]ₛₒ specₜ)
--     (oa : OracleComp spec₁ α) (s : σ × τ) :
--     simulate' (so ++ₛₒ so') s ↑oa = simulate' so s.1 oa := by
--   rw [simulate'_def (so ++ₛₒ so'), simulate_coe_append_left, Functor.map_map,
--     Function.comp, simulate'_def]

-- port: remaining lemmas here

end subSpec

end SimOracle
