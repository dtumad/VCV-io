/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Simulate

/-!
# Basic Constructions of Simulation Oracles

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

section compose

variable {spec₁ spec₂ specₜ : OracleSpec} {σ τ : Type}

/-- Given a simulation oracle `so` from `spec₁` to `spec₂` and a simulation oracle `so'` from
`spec₂` to a final target set of oracles `specₜ`, construct a new simulation oracle
from `spec₁` to `spec₂` by first substituting queries using `so`, and then further
substituting with the oracles in `so'`. -/
def compose (so : spec₁ →[σ]ₛₒ spec₂) (so' : spec₂ →[τ]ₛₒ specₜ) :
    spec₁ →[σ × τ]ₛₒ specₜ :=
  λ i ⟨t, s₁, s₂⟩ ↦ (λ ⟨⟨t, s₁⟩, s₂⟩ ↦ ⟨t, s₁, s₂⟩) <$>
    simulate so' (so i (t, s₁)) s₂

infixl : 65 " ∘ₛₒ " => λ so' so ↦ compose so so'

@[simp]
lemma compose_apply (so : spec₁ →[σ]ₛₒ spec₂) (so' : spec₂ →[τ]ₛₒ specₜ)
  (i : spec₁.ι) : (so' ∘ₛₒ so) i = λ ⟨t, s₁, s₂⟩ ↦ (λ ⟨⟨t, s₁⟩, s₂⟩ ↦ ⟨t, s₁, s₂⟩) <$>
    simulate so' (so i (t, s₁)) s₂ := rfl

end compose

variable {spec specₜ : OracleSpec} {σ τ : Type}

section maskState

/-- Substitute an equivalent type for the state of a simulation oracle, by using the equivalence
to move back and forth between the states as needed.
This can be useful when operations such like `simOracle.append` add on a state of type `Unit`.-/
def maskState (so : spec →[σ]ₛₒ specₜ) (e : σ ≃ τ) : spec →[τ]ₛₒ specₜ :=
  λ i ⟨t, s⟩ ↦ map id e <$> so i (t, e.symm s)

@[simp]
lemma maskState_apply (so : spec →[σ]ₛₒ specₜ) (e : σ ≃ τ) (i : spec.ι) :
  so.maskState e i = λ ⟨t, s⟩ ↦ map id e <$> so i (t, e.symm s) := rfl

end maskState

end SimOracle

/-- "Simulate" a computation using the original oracles by "replacing" queries with queries.
This operates as an actual identity for `simulate'`, in that we get an exact equality
between the new and original computation.

This can be useful especially with `SimOracle.append`, in order to simulate a single oracle
in a larger set of oracles, leaving the behavior of other oracles unchanged.

This is importantly different than `unifOracle`, which preserves probabilities but
changes the target oracle spec to `unifSpec` by explicitly choosing outputs randomly. -/
def idOracle (spec : OracleSpec) : spec →ₛₒ spec :=
  λ i ⟨t, ()⟩ ↦ ((., ())) <$> query i t

namespace idOracle

variable (spec : OracleSpec)

@[simp]
lemma apply_eq : idOracle spec i = λ ⟨t, ()⟩ ↦ ((., ())) <$> query i t := rfl

@[simp]
lemma simulate_eq (oa : OracleComp spec α) (s : Unit) :
    simulate (idOracle _) oa s = ((·, ())) <$> oa := by
  revert s
  induction oa using OracleComp.inductionOn with
  | h_pure x => exact λ _ ↦ rfl
  | h_query_bind i t oa hoa =>
      exact λ () ↦ by simp [map_eq_bind_pure_comp, hoa]

@[simp]
lemma simulate'_eq (oa : OracleComp spec α) (s : Unit) :
    simulate' (idOracle _) oa s = oa := by
  simp [simulate', Functor.map_map, Function.comp]

end idOracle
