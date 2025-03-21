/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.Support
import ToMathlib.Control.StateT

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

universe u v w

variable {ι ιₜ : Type*} {spec : OracleSpec ι} {specₜ : OracleSpec ιₜ}
    {m : Type u → Type v} {α β γ σ : Type u}

/-- Specifies a way to simulate a set of oracles using another set of oracles.
e.g. using uniform selection oracles with a query cache to simulate a random oracle.
`simulateQ` gives a method for applying a simulation oracle to a specific computation. -/
@[ext]
structure QueryImpl {ι : Type w} (spec : OracleSpec ι) (m : Type u → Type v) where
  impl {α : Type u} (q : OracleQuery spec α) : m α

instance QueryImpl.Inhabited [∀ i, Inhabited (spec.range i)] [Pure m] :
  Inhabited (QueryImpl spec m) := ⟨{impl q := pure q.defaultOutput}⟩

lemma QueryImpl.ext' {so so' : QueryImpl spec m}
    (h : ∀ {α} (q : OracleQuery spec α), so.impl q = so'.impl q) :
    so = so' := QueryImpl.ext (funext λ _ ↦ funext λ q ↦ h q)

namespace OracleComp

section simulateQ

/-- Canonical lifting of a function `OracleQuery spec α → m α`
to a new function `OracleComp spec α` by preserving `bind`, `pure`, and `failure`.
NOTE: could change the output type to `OracleComp spec →ᵐ m`, makes some stuff below free -/
def simulateQ [AlternativeMonad m] [LawfulAlternative m]
    (so : QueryImpl spec m) (oa : OracleComp spec α) : m α :=
  OptionT.mapM' (FreeMonad.mapM' m so.impl) oa

variable [AlternativeMonad m] [LawfulAlternative m] (so : QueryImpl spec m)

@[simp]
lemma simulateQ_failure : simulateQ so (failure : OracleComp spec α) = failure :=
  OptionT.mapM'_failure (FreeMonad.mapM' m so.impl)

@[simp]
lemma simulateQ_query (q : OracleQuery spec α) : simulateQ so q = so.impl q := by
  simp [simulateQ, OracleComp.liftM_def]

@[simp]
lemma simulateQ_pure (x : α) : simulateQ so (pure x) = pure x :=
  MonadHom.mmap_pure _ x

@[simp]
lemma simulateQ_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    simulateQ so (oa >>= ob) = simulateQ so oa >>= fun x => simulateQ so (ob x) :=
  MonadHom.mmap_bind _ oa ob

@[simp]
lemma simulateQ_map (oa : OracleComp spec α) (f : α → β) :
    simulateQ so (f <$> oa) = f <$> simulateQ so oa := by simp [map_eq_bind_pure_comp]

@[simp]
lemma simulateQ_seq (og : OracleComp spec (α → β)) (oa : OracleComp spec α) :
    simulateQ so (og <*> oa) = simulateQ so og <*> simulateQ so oa := by simp [seq_eq_bind]

@[simp]
lemma simulateQ_seqLeft (oa : OracleComp spec α) (ob : OracleComp spec β) :
    simulateQ so (oa <* ob) = simulateQ so oa <* simulateQ so ob := by simp [seqLeft_eq]

@[simp]
lemma simulateQ_seqRight (oa : OracleComp spec α) (ob : OracleComp spec β) :
    simulateQ so (oa *> ob) = simulateQ so oa *> simulateQ so ob := by simp [seqRight_eq]

@[simp]
lemma simulateQ_ite (p : Prop) [Decidable p] (oa oa' : OracleComp spec α) :
    simulateQ so (ite p oa oa') = ite p (simulateQ so oa) (simulateQ so oa') := by
  split_ifs <;> rfl

end simulateQ

section simulate

/-- `simulate so oa s` runs the computation `oa`, using the simulation oracle `so` to
answer any queries to the oracle, starting the simulation oracle's state with `s`.
TODO: deprecate -/
@[reducible]
def simulate (so : QueryImpl spec (StateT σ (OracleComp specₜ))) (s : σ)
    (oa : OracleComp spec α) : OracleComp specₜ (α × σ) :=
  (simulateQ so oa).run s

/-- Version of `simulate` that tosses out the oracle state at the end. -/
@[reducible]
def simulate' (so : QueryImpl spec (StateT σ (OracleComp specₜ))) (s : σ)
    (oa : OracleComp spec α) : OracleComp specₜ α :=
  (simulateQ so oa).run' s

variable (so : QueryImpl spec (StateT σ (OracleComp specₜ)))

lemma simulate_def (s : σ) (oa : OracleComp spec α) :
    simulate so s oa = (simulateQ so oa).run s := rfl

lemma simulate'_def (s : σ) (oa : OracleComp spec α) :
    simulate' so s oa = (simulateQ so oa).run' s := rfl

section basic

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
  simp [simulate, simulateQ_bind, StateT.run_bind]

@[simp low]
lemma simulate'_bind (s : σ) (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (simulate' so s (oa >>= ob) = do let z ← simulate so s oa; simulate' so z.2 (ob z.1)) := by
  simp [simulate', simulate]

@[simp low]
lemma simulate_query (s : σ) (q : OracleQuery spec α) :
    simulate so s q = (so.impl q).run s := by
  simp [simulate', simulate]

@[simp low]
lemma simulate'_query (s : σ) (q : OracleQuery spec α) :
    simulate' so s q = (so.impl q).run' s := by
  simp [simulate']

lemma simulate_query_bind (s : σ) (q : OracleQuery spec β)
    (oa : β → OracleComp spec α) : simulate so s (q >>= oa) =
    (do let (u, s') ← (so.impl q).run s; simulate so s' (oa u)) := by
  rw [simulate_bind, simulate_query]

lemma simulate'_query_bind (s : σ) (q : OracleQuery spec β)
    (oa : β → OracleComp spec α) : simulate' so s (q >>= oa) =
    (do let (u, s') ← (so.impl q).run s; simulate' so s' (oa u)) := by
  rw [simulate'_bind, simulate_query]

@[simp low]
lemma simulate_map (s : σ) (oa : OracleComp spec α) (f : α → β) :
    simulate so s (f <$> oa) = (map f id) <$> simulate so s oa := by
  simp [simulate, map]; rfl

@[simp low]
lemma simulate'_map (s : σ) (oa : OracleComp spec α) (f : α → β) :
    simulate' so s (f <$> oa) = f <$> simulate' so s oa := by
  simp [simulate']

@[simp low]
lemma simulate_seq (s : σ) (oa : OracleComp spec α) (og : OracleComp spec (α → β)) :
    simulate so s (og <*> oa) = simulate so s og >>= λ z ↦
      (map z.1 id <$> simulate so z.2 oa) := by
  simp [seq_eq_bind]

@[simp low]
lemma simulate'_seq (s : σ) (oa : OracleComp spec α) (og : OracleComp spec (α → β)) :
    simulate' so s (og <*> oa) = simulate so s og >>= λ z ↦
      (z.1 <$> simulate' so z.2 oa) := by
  simp [simulate']

end basic

section support

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
  rw [simulate', StateT.run', support_map, Set.image_subset_iff]
  apply support_simulate_subset_preimage_support

lemma mem_support_simulate'_of_mem_support_simulate {oa : OracleComp spec α} {s : σ} {x : α}
    (s' : σ) (h : (x, s') ∈ (simulate so s oa).support) : x ∈ (simulate' so s oa).support := by
  simp only [support_simulate', Set.fmap_eq_image, Set.mem_image, Prod.exists, exists_and_right,
    exists_eq_right]
  exact ⟨s', h⟩

end support

section subsingleton

variable {σ : Type u} [Subsingleton σ] (so : QueryImpl spec (StateT σ (OracleComp specₜ)))

/-- If the state type is `Subsingleton`, then we can represent simulation in terms of `simulate'`,
adding back any state at the end of the computation. -/
lemma simulate_eq_map_simulate'_of_subsingleton (oa : OracleComp spec α) (s s' : σ) :
    simulate so s oa = (·, s') <$> simulate' so s oa := by
  have : (λ x : α × σ ↦ (x.1, s')) = id :=
    funext λ (x, s) ↦ Prod.eq_iff_fst_eq_snd_eq.2 ⟨rfl, Subsingleton.elim _ _⟩
  simp [simulate', simulate, this]

lemma simulate_eq_map_simulate' [Inhabited σ] (oa : OracleComp spec α) (s : σ) :
    simulate so s oa = (·, default) <$> simulate' so s oa :=
  simulate_eq_map_simulate'_of_subsingleton so oa s default

end subsingleton

end simulate

section support_test

variable {ι : Type u} {spec : OracleSpec ι} {α : Type v}

attribute [local instance] Set.monad

def supportWhen' (ox : OracleComp spec α)
    (possible_outputs : {α : Type v} → OracleQuery spec α → Set α) : Set α :=
  ox.simulateQ ⟨possible_outputs⟩

def support' (oa : OracleComp spec α) : Set α :=
  oa.simulateQ ⟨fun | query i t => Set.univ⟩

end support_test

end OracleComp
