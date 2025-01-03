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
-- def SimOracle {ι ιₜ : Type} (spec : OracleSpec ι) (specₜ : OracleSpec ιₜ) (σ : Type) :=
--   (i : ι) → spec.domain i → σ → OracleComp specₜ (spec.range i × σ)

def SimOracle {ι ιₜ : Type} (spec : OracleSpec ι) (specₜ : OracleSpec ιₜ)
    (σ : Type) := (i : ι) → spec.domain i → StateT σ (OracleComp specₜ) (spec.range i)

notation : 55 spec " →[" σ "]ₛₒ " specₜ => SimOracle spec specₜ σ

-- notation : 55 spec " →[" σ "]ₛₒₜ " specₜ => SimOracleT spec specₜ σ


variable {ι ιₜ : Type} {spec : OracleSpec ι} {specₜ : OracleSpec ιₜ} {α β σ : Type}

instance SimOracle.Inhabited [spec.FiniteRange] :
  Inhabited (spec →[σ]ₛₒ specₜ) := ⟨λ _ _ s ↦ pure ⟨default, s⟩⟩

namespace OracleComp

def simulateT {α : Type} (so : spec →[σ]ₛₒ specₜ)
    (oa : OracleComp spec α) : StateT σ (OracleComp specₜ) α := by
  induction oa using OracleComp.construct with
  | pure x => exact pure x
  | query_bind i t oa r => exact so i t >>= r
  | failure => exact failure

/-- `simulate so oa s` runs the computation `oa`, using the simulation oracle `so` to
answer any queries to the oracle, starting the simulation oracle's state with `s`. -/
def simulate {α : Type} (so : spec →[σ]ₛₒ specₜ) (s : σ) :
    (oa : OracleComp spec α) → OracleComp specₜ (α × σ) := λ oa ↦
  (simulateT so oa).run s

/-- Version of `simulate` that tosses out the oracle state at the end.
TODO: should this be an alias/notation? -/
def simulate' (so : spec →[σ]ₛₒ specₜ) (s : σ) (oa : OracleComp spec α) : OracleComp specₜ α :=
  (simulateT so oa).run' s

lemma simulate'_def (so : spec →[σ]ₛₒ specₜ) (s : σ) (oa : OracleComp spec α) :
    simulate' so s oa = fst <$> simulate so s oa := rfl

section basic

variable {σ : Type} (so : spec →[σ]ₛₒ specₜ)

@[simp low]
lemma simulate_pure (s : σ) (x : α) : simulate so s (pure x) = pure (x, s) := rfl

@[simp low]
lemma simulate'_pure (s : σ) (x : α) : simulate' so s (pure x) = pure x := rfl

@[simp]
lemma simulate_failure (s : σ) : simulate so s (failure : OracleComp spec α) = failure := rfl

@[simp]
lemma simulate'_failure (s : σ) : simulate' so s (failure : OracleComp spec α) = failure := rfl

@[simp low]
lemma simulate_bind (s : σ)  (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (simulate so s (oa >>= ob) = do let z ← simulate so s oa; simulate so z.2 (ob z.1)) := by
  revert s
  sorry
  -- induction oa using OracleComp.inductionOn with
  -- | pure x => exact (λ _ ↦ rfl)
  -- | query_bind i t oa hoa =>
  --     simp only [simulate, OracleComp.bind'_eq_bind, pure_bind, hoa, bind_assoc, implies_true]
  -- | failure => simp [simulate]

@[simp low]
lemma simulate'_bind (s : σ) (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (simulate' so s (oa >>= ob) = do let z ← simulate so s oa; simulate' so z.2 (ob z.1)) := by
  sorry --simp only [simulate', simulate_bind, map_bind]

@[simp low]
lemma simulate_query (s : σ) (i : ι) (t : spec.domain i) :
    simulate so s (query i t) = so i t s := by
  sorry --simp_rw [query_def, simulate, Prod.mk.eta, bind_pure]

@[simp low]
lemma simulate'_query (s : σ) (i : ι) (t : spec.domain i) :
    simulate' so s (query i t) = fst <$> so i t s := by
  sorry --rw [simulate', simulate_query]

lemma simulate_query_bind (s : σ) (i : ι) (t : spec.domain i)
    (oa : spec.range i → OracleComp spec α) : simulate so s (query i t >>= oa) =
    (do let (u, s') ← so i t s; simulate so s' (oa u)) := by
  rw [simulate_bind, simulate_query]

lemma simulate'_query_bind (s : σ) (i : ι) (t : spec.domain i)
    (oa : spec.range i → OracleComp spec α) : simulate' so s (query i t >>= oa) =
    (do let (u, s') ← so i t s; simulate' so s' (oa u)) := by
  rw [simulate'_bind, simulate_query]

@[simp low]
lemma simulate_map (s : σ) (oa : OracleComp spec α) (f : α → β) :
    simulate so s (f <$> oa) = (map f id) <$> simulate so s oa := by
  simp [map_eq_bind_pure_comp, Function.comp, Prod.map]
  rfl

@[simp low]
lemma simulate'_map (s : σ) (oa : OracleComp spec α) (f : α → β) :
    simulate' so s (f <$> oa) = f <$> simulate' so s oa := by
  sorry --simp [simulate', map_eq_bind_pure_comp, Function.comp, Prod.map]

@[simp low]
lemma simulate_seq (s : σ) (oa : OracleComp spec α) (og : OracleComp spec (α → β)) :
    simulate so s (og <*> oa) = simulate so s og >>= λ z ↦
      (map z.1 id <$> simulate so z.2 oa) := by
  simp [seq_eq_bind]

@[simp low]
lemma simulate'_seq (s : σ) (oa : OracleComp spec α) (og : OracleComp spec (α → β)) :
    simulate' so s (og <*> oa) = simulate so s og >>= λ z ↦
      (z.1 <$> simulate' so z.2 oa) := by
  sorry --simp [simulate', map_bind, map_eq_bind_pure_comp]

end basic

section support

variable {σ : Type} (so : spec →[σ]ₛₒ specₜ)

lemma support_simulate' (oa : OracleComp spec α) (s : σ) :
    (simulate' so s oa).support = fst <$> (simulate so s oa).support :=
  support_map _ fst

/-- Since `support` assumes any possible query result, `simulate` will never reduce the support.
In particular the support of a simulation lies in the preimage of the original support. -/
lemma support_simulate_subset_preimage_support (oa : OracleComp spec α) (s : σ) :
    (simulate so s oa).support ⊆ fst ⁻¹' oa.support := by
  revert s
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind i t oa hoa =>
      simp [hoa]
      refine λ _ t s' _ ↦ Set.subset_iUnion_of_subset t (hoa t s')
  | failure => simp

/-- Simulation only reduces the possible oracle outputs, so can't reduce the support. In particular
the first output of a simulation has support at most that of the original computation -/
lemma support_simulate'_subset_support (oa : OracleComp spec α) (s : σ) :
    (simulate' so s oa).support ⊆ oa.support := by
  sorry
  -- rw [simulate', support_map, Set.image_subset_iff]
  -- apply support_simulate_subset_preimage_support

lemma mem_support_simulate'_of_mem_support_simulate {oa : OracleComp spec α} {s : σ} {x : α}
    (s' : σ) (h : (x, s') ∈ (simulate so s oa).support) : x ∈ (simulate' so s oa).support := by
  simp only [support_simulate', Set.fmap_eq_image, Set.mem_image, Prod.exists, exists_and_right,
    exists_eq_right]
  exact ⟨s', h⟩

end support

section stateIndep

variable {σ : Type} (so : spec →[σ]ₛₒ spec)

lemma simulate'_eq_self (h : ∀ i t s, fst <$> so i t s = query i t)
    (s : σ) (oa : OracleComp spec α) : simulate' so s oa = oa := by
  revert s
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind i t oa hoa => refine λ s ↦ by simp_rw [simulate'_bind, simulate_query,
      hoa, ← h i t s, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  | failure => simp

-- TODO: this for various oracles?
class StateIndep (so : spec →[σ]ₛₒ spec) where
    state_indep : ∀ i t s, fst <$> so i t s = query i t

@[simp]
lemma simulate'_eq_self_of_stateIndep (so : spec →[σ]ₛₒ spec) [h : StateIndep so]
    (s : σ) (oa : OracleComp spec α) : simulate' so s oa = oa :=
  simulate'_eq_self so (h.state_indep) s oa

@[simp]
lemma fst_map_simulate_eq_self_of_stateIndep (so : spec →[σ]ₛₒ spec) [StateIndep so]
    (s : σ) (oa : OracleComp spec α) : fst <$> (simulate so s oa) = oa :=
  simulate'_eq_self_of_stateIndep so s oa

lemma mem_support_of_mem_support_simulate' {so : spec →[σ]ₛₒ spec} [h : StateIndep so]
    {s : σ} {oa : OracleComp spec α} {x : α}
    (h : x ∈ (simulate' so s oa).support) : x ∈ oa.support := by
  rwa [simulate'_eq_self_of_stateIndep] at h

end stateIndep

section idem

variable {σ : Type} (so : spec →[σ]ₛₒ spec)

/-- If `fst <$> so i (t, s)` has the same distribution as `query i t` for any state `s`,
Then `simulate' so` doesn't change the output distribution.
Stateless oracles are the most common example of this -/
lemma evalDist_simulate'_eq_evalDist [spec.FiniteRange]
    (h : ∀ i t s, evalDist (fst <$> so i t s) = OptionT.lift (PMF.uniformOfFintype (spec.range i)))
    (s : σ) (oa : OracleComp spec α) : evalDist (simulate' so s oa) = evalDist oa := by
  revert s
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind i t oa hoa => exact (λ s ↦ by
      simp only [simulate'_bind, simulate_query, evalDist_bind, Function.comp_def, hoa,
        evalDist_query, ← h i t s, evalDist_map, PMF.bind_map, hoa, bind_map_left])
  | failure => simp

end idem

section subsingleton

variable {σ : Type} [Subsingleton σ] (so : spec →[σ]ₛₒ specₜ)

/-- If the state type is `Subsingleton`, then we can represent simulation in terms of `simulate'`,
adding back any state at the end of the computation. -/
lemma simulate_eq_map_simulate'_of_subsingleton (oa : OracleComp spec α) (s s' : σ) :
    simulate so s oa = (·, s') <$> simulate' so s oa := by
  simp only [simulate', map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  convert symm (bind_pure (simulate so s oa))
  sorry

lemma simulate_eq_map_simulate' [Inhabited σ] (oa : OracleComp spec α) (s : σ) :
    simulate so s oa = (·, default) <$> simulate' so s oa :=
  simulate_eq_map_simulate'_of_subsingleton so oa s default

end subsingleton

end OracleComp
