/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.EvalDist

/-!
# Simulation Semantics for Oracles in a Computation

This file defines a type `SimOracle spec specₜ σ` to represent a way to simulate
oracles in `spec` using the oracles in `specₜ`, maintaining some state of type `σ`.
We then define a function `simulate so oa s` to simulate the computation `oa`
using `so` to answer oracle queries, with initial state `s`.
-/

open OracleSpec OracleComp Prod Sum

/-- Specifies a way to simulate a set of oracles using another set of oracles.
e.g. using uniform selection oracles with a query cache to simulate a random oracle.
`simulate` gives a method for applying a simulation oracle to a specific computation. -/
def SimOracle (spec specₜ : OracleSpec) (σ : Type) :=
  (i : spec.ι) → spec.domain i × σ → OracleComp specₜ (spec.range i × σ)

notation : 55 spec "→[" σ "]ₛₒ" specₜ => SimOracle spec specₜ σ
notation : 55 spec "→ₛₒ" specₜ => SimOracle spec specₜ Unit

instance (spec specₜ : OracleSpec) (σ : Type) :
    Inhabited (spec →[σ]ₛₒ specₜ) := ⟨λ _ ⟨_, s⟩ ↦ pure (default, s)⟩

/-- `simulate so oa s` runs the computation `oa`, using the simulation oracle `so` to
answer any queries to the oracle, starting the simulation oracle's state with `s`. -/
def simulate (so : spec →[σ]ₛₒ specₜ) : OracleComp spec α → σ → OracleComp specₜ (α × σ)
  | pure' α x, s => return (x, s)
  | query_bind' i t α oa, s => do
      let ⟨u, s'⟩ ← so i (t, s)
      simulate so (oa u) s'

/-- Version of `simulate` that tosses out the oracle state at the end. -/
def simulate' (so : spec →[σ]ₛₒ specₜ) (oa : OracleComp spec α) (s : σ) :
    OracleComp specₜ α :=
  fst <$> simulate so oa s

namespace OracleComp

variable {spec specₜ : OracleSpec} {α β γ σ : Type}
  (so : spec →[σ]ₛₒ specₜ)

section basic

@[simp]
lemma simulate_pure (x : α) (s : σ) : simulate so (pure x) s = pure (x, s) := rfl

@[simp]
lemma simulate'_pure (x : α) (s : σ) : simulate' so (pure x) s = pure x := rfl

@[simp]
lemma simulate_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (s : σ) : (simulate so (oa >>= ob) s = do
      let ⟨x, s'⟩ ← simulate so oa s
      simulate so (ob x) s') := by
  revert s
  induction oa using OracleComp.inductionOn with
  | h_pure x => exact (λ _ ↦ rfl)
  | h_query_bind i t oa hoa =>
      simp only [simulate, OracleComp.bind'_eq_bind, pure_bind, hoa, bind_assoc, implies_true]

@[simp]
lemma simulate'_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (s : σ) : (simulate' so (oa >>= ob) s = do
      let ⟨x, s'⟩ ← simulate so oa s
      simulate' so (ob x) s') := by
  simp only [simulate', simulate_bind, map_bind]

@[simp]
lemma simulate_query (i : spec.ι) (t : spec.domain i) (s : σ) :
    simulate so (query i t) s = so i (t, s) := by
  simp_rw [query_def, simulate, Prod.mk.eta, bind_pure]

@[simp]
lemma simulate'_query (i : spec.ι) (t : spec.domain i) (s : σ) :
    simulate' so (query i t) s = fst <$> so i (t, s) := by
  rw [simulate', simulate_query]

@[simp]
lemma simulate_map (oa : OracleComp spec α) (f : α → β) (s : σ) :
    simulate so (f <$> oa) s = (map f id) <$> simulate so oa s := by
  simp [map_eq_bind_pure_comp, Function.comp]

@[simp]
lemma simulate'_map (oa : OracleComp spec α) (f : α → β) (s : σ) :
    simulate' so (f <$> oa) s = f <$> simulate' so oa s := by
  simp [simulate', simulate_map, Functor.map_map, Function.comp]

end basic

section support

/-- Since `support` assumes any possible query result, `simulate` will never reduce the support.
In particular the support of a simulation lies in the preimage of the original support. -/
lemma support_simulate_subset_preimage_support (oa : OracleComp spec α) (s : σ) :
    (simulate so oa s).support ⊆ fst ⁻¹' oa.support := by
  revert s
  induction oa using OracleComp.inductionOn with
  | h_pure x => simp
  | h_query_bind i t oa hoa =>
      simp [hoa]
      refine λ _ t s' _ ↦ Set.subset_iUnion_of_subset t (hoa t s')

/-- Simulation only reduces the possible oracle outputs, so can't reduce the support. In particular
the first output of a simulation has support at most that of the original computation -/
lemma support_simulate'_subset_support (oa : OracleComp spec α) (s : σ) :
    (simulate' so oa s).support ⊆ oa.support := by
  rw [simulate', support_map, Set.image_subset_iff]
  apply support_simulate_subset_preimage_support

end support

end OracleComp
