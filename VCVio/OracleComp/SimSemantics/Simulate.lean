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

We mark lemmas regarding simulating specific computations as `@[simp low]`,
so that lemmas specific to certain simulation oracles get applied firts.
For example `idOracle` has no effect upon simulation, and we should apply that fact first.
-/

open OracleSpec Prod

/-- Specifies a way to simulate a set of oracles using another set of oracles.
e.g. using uniform selection oracles with a query cache to simulate a random oracle.
`simulate` gives a method for applying a simulation oracle to a specific computation. -/
def SimOracle {ι ιₜ : Type} (spec : OracleSpec ι) (specₜ : OracleSpec ιₜ) (σ : Type) :=
  (i : ι) → spec.domain i → σ → OracleComp specₜ (spec.range i × σ)

notation : 55 spec " →[" σ "]ₛₒ " specₜ => SimOracle spec specₜ σ

variable {ι ιₜ : Type} {spec : OracleSpec ι} {specₜ : OracleSpec ιₜ} {α β σ : Type}

instance SimOracle.Inhabited : Inhabited (spec →[σ]ₛₒ specₜ) := ⟨λ _ _ s ↦ pure (default, s)⟩

namespace OracleComp

/-- `simulate so oa s` runs the computation `oa`, using the simulation oracle `so` to
answer any queries to the oracle, starting the simulation oracle's state with `s`. -/
def simulate {α : Type} (so : spec →[σ]ₛₒ specₜ) (s : σ) :
    (oa : OracleComp spec α) → OracleComp specₜ (α × σ)
  | pure' α x => return (x, s)
  | queryBind' i t α oa => do
      let (u, s') ← so i t s
      simulate so s' (oa u)

/-- Version of `simulate` that tosses out the oracle state at the end. -/
def simulate' (so : spec →[σ]ₛₒ specₜ) (s : σ) (oa : OracleComp spec α) : OracleComp specₜ α :=
  fst <$> simulate so s oa

lemma simulate'_def (so : spec →[σ]ₛₒ specₜ) (s : σ) (oa : OracleComp spec α) :
    simulate' so s oa = fst <$> simulate so s oa := rfl

section basic

variable {σ : Type} (so : spec →[σ]ₛₒ specₜ)

@[simp low]
lemma simulate_pure (s : σ) (x : α) : simulate so s (pure x) = pure (x, s) := rfl

@[simp low]
lemma simulate'_pure (s : σ) (x : α) : simulate' so s (pure x) = pure x := rfl

@[simp low]
lemma simulate_bind (s : σ)  (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (simulate so s (oa >>= ob) = do let z ← simulate so s oa; simulate so z.2 (ob z.1)) := by
  revert s
  induction oa using OracleComp.inductionOn with
  | h_pure x => exact (λ _ ↦ rfl)
  | h_queryBind i t oa hoa =>
      simp only [simulate, OracleComp.bind'_eq_bind, pure_bind, hoa, bind_assoc, implies_true]

@[simp low]
lemma simulate'_bind (s : σ) (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (simulate' so s (oa >>= ob) = do let z ← simulate so s oa; simulate' so z.2 (ob z.1)) := by
  simp only [simulate', simulate_bind, map_bind]

@[simp low]
lemma simulate_query (s : σ) (i : ι) (t : spec.domain i) :
    simulate so s (query i t) = so i t s := by
  simp_rw [query_def, simulate, Prod.mk.eta, bind_pure]

@[simp low]
lemma simulate'_query (s : σ) (i : ι) (t : spec.domain i) :
    simulate' so s (query i t) = fst <$> so i t s := by
  rw [simulate', simulate_query]

@[simp low]
lemma simulate_map (s : σ) (oa : OracleComp spec α) (f : α → β) :
    simulate so s (f <$> oa) = (map f id) <$> simulate so s oa := by
  simp [map_eq_bind_pure_comp, Function.comp, Prod.map]

@[simp low]
lemma simulate'_map (s : σ) (oa : OracleComp spec α) (f : α → β) :
    simulate' so s (f <$> oa) = f <$> simulate' so s oa := by
  simp [simulate', map_eq_bind_pure_comp, Function.comp, Prod.map]

@[simp low]
lemma simulate_seq (s : σ) (oa : OracleComp spec α) (og : OracleComp spec (α → β)) :
    simulate so s (og <*> oa) = simulate so s og >>= λ z ↦
      (map z.1 id <$> simulate so z.2 oa) := by
  simp [seq_eq_bind]

@[simp low]
lemma simulate'_seq (s : σ) (oa : OracleComp spec α) (og : OracleComp spec (α → β)) :
    simulate' so s (og <*> oa) = simulate so s og >>= λ z ↦
      (z.1 <$> simulate' so z.2 oa) := by
  simp [simulate', map_bind, map_eq_bind_pure_comp]

end basic

section support

variable {σ : Type} (so : spec →[σ]ₛₒ specₜ)

/-- Since `support` assumes any possible query result, `simulate` will never reduce the support.
In particular the support of a simulation lies in the preimage of the original support. -/
lemma support_simulate_subset_preimage_support (oa : OracleComp spec α) (s : σ) :
    (simulate so s oa).support ⊆ fst ⁻¹' oa.support := by
  revert s
  induction oa using OracleComp.inductionOn with
  | h_pure x => simp
  | h_queryBind i t oa hoa =>
      simp [hoa]
      refine λ _ t s' _ ↦ Set.subset_iUnion_of_subset t (hoa t s')

/-- Simulation only reduces the possible oracle outputs, so can't reduce the support. In particular
the first output of a simulation has support at most that of the original computation -/
lemma support_simulate'_subset_support (oa : OracleComp spec α) (s : σ) :
    (simulate' so s oa).support ⊆ oa.support := by
  rw [simulate', support_map, Set.image_subset_iff]
  apply support_simulate_subset_preimage_support

end support

section idem

variable {σ : Type} (so : spec →[σ]ₛₒ spec)

lemma simulate'_eq_self (h : ∀ i t s, fst <$> so i t s = query i t)
    (s : σ) (oa : OracleComp spec α) : simulate' so s oa = oa := by
  revert s
  induction oa using OracleComp.inductionOn with
  | h_pure x => simp
  | h_queryBind i t oa hoa => refine λ s ↦ by simp_rw [simulate'_bind, simulate_query,
      hoa, ← h i t s, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]

/-- If `fst <$> so i (t, s)` has the same distribution as `query i t` for any state `s`,
Then `simulate' so` doesn't change the output distribution.
Stateless oracles are the most common example of this -/
lemma evalDist_simulate'_eq_evalDist
    (h : ∀ i t s, evalDist (fst <$> so i t s) = PMF.uniformOfFintype (spec.range i))
    (s : σ) (oa : OracleComp spec α) : evalDist (simulate' so s oa) = evalDist oa := by
  revert s
  induction oa using OracleComp.inductionOn with
  | h_pure x => simp
  | h_queryBind i t oa hoa => refine (λ s ↦
      by simp only [simulate'_bind, simulate_query, evalDist_bind, Function.comp, hoa,
        evalDist_query, ← h i t s, evalDist_map, PMF.bind_map])

end idem

section subsingleton

variable {σ : Type} [Subsingleton σ] (so : spec →[σ]ₛₒ specₜ)

/-- If the state type is `Subsingleton`, then we can represent simulation in terms of `simulate'`,
adding back any state at the end of the computation. -/
lemma simulate_eq_map_simulate'_of_subsingleton (oa : OracleComp spec α) (s s' : σ) :
    simulate so s oa = (·, s') <$> simulate' so s oa := by
  simp only [simulate', map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  convert symm (bind_pure (simulate so s oa))

lemma simulate_eq_map_simulate' [Inhabited σ] (oa : OracleComp spec α) (s : σ) :
    simulate so s oa = (·, default) <$> simulate' so s oa :=
  simulate_eq_map_simulate'_of_subsingleton so oa s default

-- TODO: versions for dist semantics stuff

end subsingleton

end OracleComp
