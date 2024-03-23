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

open OracleSpec OracleComp Prod Sum

/-- Specifies a way to simulate a set of oracles using another set of oracles.
e.g. using uniform selection oracles with a query cache to simulate a random oracle.
`simulate` gives a method for applying a simulation oracle to a specific computation. -/
def SimOracle (spec₁ spec₂ : OracleSpec) (σ : Type) :=
  (i : spec₁.ι) → spec₁.domain i × σ → OracleComp spec₂ (spec₁.range i × σ)

notation : 55 spec₁ "→[" σ "]ₛₒ" spec₂ => SimOracle spec₁ spec₂ σ
notation : 55 spec₁ "→ₛₒ" spec₂ => SimOracle spec₁ spec₂ Unit

instance (spec₁ spec₂ : OracleSpec) (σ : Type) [h : Nonempty σ] :
    Nonempty (spec₁ →[σ]ₛₒ spec₂) :=
  h.elim (λ s ↦ ⟨λ _ _ ↦ return (default, s)⟩)
instance (spec₁ spec₂ : OracleSpec) (σ : Type) [Inhabited σ] : Inhabited (spec₁ →[σ]ₛₒ spec₂) :=
  ⟨λ _ _ ↦ return default⟩

/-- `simulate so oa s` runs the computation `oa`, using the simulation oracle `so` to
answer any queries to the oracle, starting the simulation oracle's state with `s`. -/
def simulate (so : spec₁ →[σ]ₛₒ spec₂) : OracleComp spec₁ α → σ → OracleComp spec₂ (α × σ)
  | pure' α x, s => return (x, s)
  | query_bind' i t α oa, s => do
      let ⟨u, s'⟩ ← so i (t, s)
      simulate so (oa u) s'

/-- Version of `simulate` that tosses out the oracle state at the end. -/
def simulate' (so : spec₁ →[σ]ₛₒ spec₂) (oa : OracleComp spec₁ α) (s : σ) :
    OracleComp spec₂ α :=
  fst <$> simulate so oa s

-- lemma simulate'.def (so : spec₁ →[σ]ₛₒ spec₂) (oa : OracleComp spec₁ α) (s : σ) :
--     simulate' so oa s = fst <$> simulate so oa s := rfl

namespace OracleComp

variable {spec₁ spec₂ : OracleSpec} {α β γ σ : Type}
  (so : spec₁ →[σ]ₛₒ spec₂)

section basic

@[simp]
lemma simulate_pure (x : α) (s : σ) : simulate so (pure x) s = pure (x, s) := rfl

@[simp]
lemma simulate'_pure (x : α) (s : σ) : simulate' so (pure x) s = pure x := rfl

@[simp]
lemma simulate_bind (oa : OracleComp spec₁ α) (ob : α → OracleComp spec₁ β)
    (s : σ) : (simulate so (oa >>= ob) s = do
      let ⟨x, s'⟩ ← simulate so oa s
      simulate so (ob x) s') := by
  revert s
  induction oa using OracleComp.inductionOn with
  | h_pure x => exact (λ _ ↦ rfl)
  | h_query_bind i t oa hoa =>
      simp only [simulate, OracleComp.bind'_eq_bind, pure_bind, hoa, bind_assoc, implies_true]

@[simp]
lemma simulate'_bind (oa : OracleComp spec₁ α) (ob : α → OracleComp spec₁ β)
    (s : σ) : (simulate' so (oa >>= ob) s = do
      let ⟨x, s'⟩ ← simulate so oa s
      simulate' so (ob x) s') := by
  simp only [simulate', simulate_bind, map_bind]

@[simp]
lemma simulate_query (i : spec₁.ι) (t : spec₁.domain i) (s : σ) :
    simulate so (query i t) s = so i (t, s) := by
  simp_rw [query_def, simulate, Prod.mk.eta, bind_pure]

@[simp]
lemma simulate'_query (i : spec₁.ι) (t : spec₁.domain i) (s : σ) :
    simulate' so (query i t) s = fst <$> so i (t, s) := by
  rw [simulate', simulate_query]

@[simp]
lemma simulate_map (oa : OracleComp spec₁ α) (f : α → β) (s : σ) :
    simulate so (f <$> oa) s = (map f id) <$> simulate so oa s := by
  simp [map_eq_bind_pure_comp, Function.comp]

@[simp]
lemma simulate'_map (oa : OracleComp spec₁ α) (f : α → β) (s : σ) :
    simulate' so (f <$> oa) s = f <$> simulate' so oa s := by
  simp [simulate', simulate_map, Functor.map_map, Function.comp]

end basic

section support

/-- Since `support` assumes any possible query result, `simulate` will never reduce the support.
In particular the support of a simulation lies in the preimage of the original support. -/
lemma support_simulate_subset_preimage_support (oa : OracleComp spec₁ α) (s : σ) :
    (simulate so oa s).support ⊆ fst ⁻¹' oa.support := by
  revert s
  induction oa using OracleComp.inductionOn with
  | h_pure x => simp
  | h_query_bind i t oa hoa =>
      simp [hoa]
      refine λ _ t s' _ ↦ Set.subset_iUnion_of_subset t (hoa t s')

/-- Simulation only reduces the possible oracle outputs, so can't reduce the support. In particular
the first output of a simulation has support at most that of the original computation -/
lemma support_simulate'_subset_support (oa : OracleComp spec₁ α) (s : σ) :
    (simulate' so oa s).support ⊆ oa.support := by
  rw [simulate', support_map, Set.image_subset_iff]
  apply support_simulate_subset_preimage_support

end support

end OracleComp

namespace SimOracle

section append

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

end append

section compose

/-- Given a simulation oracle `so` from `spec₁` to `spec₂` and a simulation oracle `so'` from
`spec₂` to a final target set of oracles `specₜ`, construct a new simulation oracle
from `spec₁` to `spec₂` by first substituting queries using `so`, and then further
substituting with the oracles in `so'`. -/
def compose (so : spec₁ →[σ]ₛₒ spec₂) (so' : spec₂ →[τ]ₛₒ specₜ) :
    spec₁ →[σ × τ]ₛₒ specₜ :=
  λ i ⟨t, s₁, s₂⟩ ↦ (λ ⟨⟨t, s₁⟩, s₂⟩ ↦ ⟨t, s₁, s₂⟩) <$>
    simulate so' (so i (t, s₁)) s₂

infixl : 65 " ∘ₛₒ " => λ so' so ↦ compose so so'

end compose

section maskState

-- TODO

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
