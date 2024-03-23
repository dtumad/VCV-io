/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.EvalDist

/-!
# Simulation Semantics for Oracles in a Computation

This file defines a type `SimOracle spec₁ spec₂ σ` to represent a way to simulate
oracles in `spec₁` using the oracles in `spec₂`, maintaining some state of type `σ`.
We then define a function `simulate so oa s` to simulate the computation `oa`
using `so` to answer oracle queries, with initial state `s`.
-/

open OracleSpec OracleComp

/-- Specifies a way to simulate a set of oracles using another set of oracles.
e.g. using uniform selection oracles with a query cache to simulate a random oracle.
`simulate` gives a method for applying a simulation oracle to a specific computation. -/
def SimOracle (spec₁ spec₂ : OracleSpec) (σ : Type) :=
  (i : spec₁.ι) → spec₁.domain i × σ → OracleComp spec₂ (spec₁.range i × σ)

notation : 55 spec₁ "→[" σ "]ₛₒ" spec₂ => SimOracle spec₁ spec₂ σ
notation : 55 spec₁ "→ₛₒ" spec₂ => SimOracle spec₁ spec₂ Unit

/-- Example of an oracle maintaining in internal incrementing value,
and returning a fake coin flip that alternates between heads and tails. -/
example : coinSpec →[ ℕ ]ₛₒ coinSpec:=
  λ () ⟨(), n⟩ ↦ return (if Even n then true else false, n + 1)

instance (spec₁ spec₂ : OracleSpec) (σ : Type) [h : Nonempty σ] : Nonempty (spec₁ →[σ]ₛₒ spec₂) :=
  h.elim (λ s ↦ ⟨λ _ _ ↦ return (default, s)⟩)
instance (spec₁ spec₂ : OracleSpec) (σ : Type) [Inhabited σ] : Inhabited (spec₁ →[σ]ₛₒ spec₂) :=
  ⟨λ _ _ ↦ return default⟩

def simulate (so : spec₁ →[σ]ₛₒ spec₂) : OracleComp spec₁ α → σ → OracleComp spec₂ (α × σ)
  | pure' α x, s => return (x, s)
  | query_bind' i t α oa, s => do
      let ⟨u, s'⟩ ← so i (t, s)
      simulate so (oa u) s'

namespace OracleComp

variable {spec₁ spec₂ : OracleSpec} {α β γ σ : Type}

lemma simulate_pure' (so : spec₁ →[σ]ₛₒ spec₂) (x : α) (s : σ) :
    simulate so (pure' α x : OracleComp spec₁ α) s = pure (x, s) := rfl

lemma simulate_query_bind' (so : spec₁ →[σ]ₛₒ spec₂) (i : spec₁.ι) (t : spec₁.domain i)
    (oa : spec₁.range i → OracleComp spec₁ α) (s : σ) :
    (simulate so (query_bind' i t α oa) s = do
      let ⟨u, s'⟩ ← so i (t, s)
      simulate so (oa u) s') := rfl

@[simp]
lemma simulate_pure (so : spec₁ →[σ]ₛₒ spec₂) (x : α) (s : σ) :
  simulate so (pure x : OracleComp spec₁ α) s = pure (x, s) := rfl

@[simp]
lemma simulate_bind (so : spec₁ →[σ]ₛₒ spec₂) (oa : OracleComp spec₁ α)
    (ob : α → OracleComp spec₁ β) (s : σ) : (simulate so (oa >>= ob) s = do
      let ⟨x, s'⟩ ← simulate so oa s
      simulate so (ob x) s') := by
  revert s
  induction oa using OracleComp.inductionOn with
  | h_pure x => exact (λ _ ↦ rfl)
  | h_query_bind i t oa hoa =>
      simp only [simulate, OracleComp.bind'_eq_bind, pure_bind, hoa, bind_assoc, implies_true]

@[simp]
lemma simulate_query (so : spec₁ →[σ]ₛₒ spec₂) (i : spec₁.ι) (t : spec₁.domain i) (s : σ) :
    simulate so (query i t) s = so i (t, s) := by
  simp_rw [query_def, simulate_query_bind', simulate_pure, Prod.mk.eta, bind_pure]

end OracleComp

namespace SimOracle

section append

open Sum

def append (so : spec₁ →[σ]ₛₒ specₜ) (so' : spec₂ →[τ]ₛₒ specₜ) :
    spec₁ ++ spec₂ →[σ × τ]ₛₒ specₜ :=
  λ i ↦ match i with
  | (inl i) => λ ⟨t, s₁, s₂⟩ ↦ do
      let ⟨u, s₁'⟩ ← so i (t, s₁) return (u, s₁', s₂)
  | (inr i) => λ ⟨t, s₁, s₂⟩ ↦ do
      let ⟨u, s₂'⟩ ← so' i (t, s₂) return (u, s₁, s₂')

infixl : 65 " ++ₛₒ " => append

end append

section compose

def compose (so : spec₁ →[σ]ₛₒ spec₂) (so' : spec₂ →[τ]ₛₒ specₜ) :
    spec₁ →[σ × τ]ₛₒ specₜ :=
  λ i ⟨t, s₁, s₂⟩ ↦ (λ ⟨⟨t, s₁⟩, s₂⟩ ↦ ⟨t, s₁, s₂⟩) <$>
    simulate so' (so i (t, s₁)) s₂

infixl : 65 " ∘ₛₒ " => λ so' so ↦ compose so so'

end compose

end SimOracle
