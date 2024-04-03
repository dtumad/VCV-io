/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.Prod

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

notation : 55 spec " →[" σ "]ₛₒ " specₜ => SimOracle spec specₜ σ
notation : 55 spec " →ₛₒ " specₜ => SimOracle spec specₜ Unit

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

lemma simulate'_def (so : spec →[σ]ₛₒ specₜ) (oa : OracleComp spec α) (s : σ) :
    simulate' so oa s = fst <$> simulate so oa s := rfl

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
      let z ← simulate so oa s
      simulate so (ob z.1) z.2) := by
  revert s
  induction oa using OracleComp.inductionOn with
  | h_pure x => exact (λ _ ↦ rfl)
  | h_query_bind i t oa hoa =>
      simp only [simulate, OracleComp.bind'_eq_bind, pure_bind, hoa, bind_assoc, implies_true]

@[simp]
lemma simulate'_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (s : σ) : (simulate' so (oa >>= ob) s = do
      let z ← simulate so oa s
      simulate' so (ob z.1) z.2) := by
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
  simp only [map_eq_bind_pure_comp, Function.comp, simulate_bind, simulate_pure, Prod_map, id_eq]

@[simp]
lemma simulate'_map (oa : OracleComp spec α) (f : α → β) (s : σ) :
    simulate' so (f <$> oa) s = f <$> simulate' so oa s := by
  simp only [simulate', simulate_map, Functor.map_map, Function.comp, Prod_map, id_eq]

lemma simulate_seq (oa : OracleComp spec α) (og : OracleComp spec (α → β)) :
    simulate so (og <*> oa) s = simulate so og s >>= λ ⟨f, s'⟩ ↦
      (map f id <$> simulate so oa s') := by
  simp only [seq_eq_bind, simulate_bind, simulate_map]

@[simp]
lemma simulate'_seq (oa : OracleComp spec α) (og : OracleComp spec (α → β)) :
    simulate' so (og <*> oa) s = simulate so og s >>= λ ⟨f, s'⟩ ↦
      (f <$> simulate' so oa s') := by
  simp only [simulate', simulate_seq, map_bind, Functor.map_map, Function.comp, Prod_map, id_eq]

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

section idem

lemma simulate'_eq_self (so : spec →[σ]ₛₒ spec) (h : ∀ i t s, fst <$> so i (t, s) = query i t)
    (oa : OracleComp spec α) :
    ∀ s, simulate' so oa s = oa := by
  induction oa using OracleComp.inductionOn with
  | h_pure x => simp
  | h_query_bind i t oa hoa => refine λ s ↦ by simp_rw [simulate'_bind, simulate_query,
      hoa, ← h i t s, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]

/-- If `fst <$> so i (t, s)` has the same distribution as `query i t` for any state `s`,
Then `simulate' so` doesn't change the output distribution.
Stateless oracles are the most common example of this -/
lemma evalDist_simulate'_eq_evalDist (so : spec →[σ]ₛₒ specₜ)
    (h : ∀ i t s, evalDist (fst <$> so i (t, s)) = PMF.uniformOfFintype (spec.range i))
    (oa : OracleComp spec α) : ∀ s, evalDist (simulate' so oa s) = evalDist oa := by
  induction oa using OracleComp.inductionOn with
  | h_pure x => simp
  | h_query_bind i t oa hoa => refine (λ s ↦
      by simp only [simulate'_bind, simulate_query, evalDist_bind, Function.comp, hoa,
        evalDist_query, ← h i t s, evalDist_map, PMF.bind_map])

end idem

section stateless

/-- If the state type is `Subsingleton`, then we can represent simulation in terms of `simulate'`,
adding back any state at the end of the computation. -/
lemma simulate_eq_map_simulate'_of_subsingleton [Subsingleton σ] (oa : OracleComp spec α)
    (s s' : σ) : simulate so oa s = (·, s') <$> simulate' so oa s := by
  simp only [simulate', map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  convert symm (bind_pure (simulate so oa s))

lemma simulate_eq_map_simulate' (so : spec →ₛₒ spec') (oa : OracleComp spec α) (s : Unit) :
    simulate so oa s = (·, ()) <$> simulate' so oa () :=
  simulate_eq_map_simulate'_of_subsingleton so oa () ()

end stateless

end OracleComp
