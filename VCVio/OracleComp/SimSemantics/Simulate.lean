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

universe u u' v v' w w' z

variable {ι ιₜ : Type*} {spec : OracleSpec ι} {specₜ : OracleSpec ιₜ}
  {α β σ : Type u}

-- T is e.g. `StateT`, `OptionT`, `WriterT`
structure SimOracle' {ι : Type u} {ιₜ : Type u'}
    (spec : OracleSpec.{u,v} ι) (specₜ : OracleSpec.{u',v'} ιₜ)
    (T : (Type w' → Type (max u' (v' + 1) w')) → Type v → Type w) where
  impl {α : Type v} (q : OracleQuery spec α) :
    T (OracleComp.{u',v',w'} specₜ) α

structure QueryImpl {ι : Type u} (spec : OracleSpec.{u,v} ι)
    (m : Type v → Type w) where
  impl {α : Type v} (q : OracleQuery spec α) : m α

/-- Specifies a way to simulate a set of oracles using another set of oracles.
e.g. using uniform selection oracles with a query cache to simulate a random oracle.
`simulate` gives a method for applying a simulation oracle to a specific computation. -/
@[ext]
structure SimOracle (spec : OracleSpec ι) (specₜ : OracleSpec ιₜ) (σ : Type u) where
  impl : {α : Type u} → OracleQuery spec α → StateT σ (OracleComp specₜ) α

notation : 55 spec " →[" σ "]ₛₒ " specₜ => SimOracle spec specₜ σ

instance SimOracle.Inhabited [∀ i, Inhabited (spec.range i)] :
  Inhabited (SimOracle spec specₜ σ) := ⟨{impl q := pure q.defaultOutput}⟩

lemma SimOracle.ext' {so so' : SimOracle spec specₜ σ}
    (h : ∀ {α} (q : OracleQuery spec α), so.impl q = so'.impl q) : so = so' :=
  SimOracle.ext (funext λ _ ↦ funext λ q ↦ h q)

namespace OracleComp

section simulateT

section new

variable {ι : Type u} {ιₜ : Type u'}
  {spec : OracleSpec.{u,v} ι} {specₜ : OracleSpec.{u',v'} ιₜ}
  {T : (Type w' → Type (max u' (v' + 1) w')) → Type v → Type w}
  [Monad (T (OracleComp specₜ))] [Alternative (T (OracleComp specₜ))]

def simulateT' (so : SimOracle' spec specₜ T) {α : Type v}
    (oa : OracleComp spec α) : T (OracleComp specₜ) α :=
  oa.mapM (fail := failure) (query_map := so.impl)

end new

section new'

variable {ι : Type u} {spec : OracleSpec.{u,v} ι}
    {m : Type v → Type w} {α : Type v}
    [Alternative m] [Monad m]

def simulateQ (so : QueryImpl spec m) (oa : OracleComp spec α) : m α :=
  oa.mapM (fail := failure) (query_map := so.impl)

noncomputable def evalDist' [spec.FiniteRange] :
    (oa : OracleComp spec α) → OptionT PMF α :=
  simulateQ ⟨fun (query i _) => OptionT.lift (PMF.uniformOfFintype (spec.range i))⟩

end new'

instance (ι : Type u) {spec : OracleSpec ι} (ω : Type u)
    [EmptyCollection ω] [Append ω] :
    Alternative (WriterT ω (OracleComp spec)) where
  failure {α} := liftM (failure : OracleComp spec α)
  orElse x y := x.run <|> (y ()).run

def simulateT (so : SimOracle spec specₜ σ)
    (oa : OracleComp spec α) : StateT σ (OracleComp specₜ) α :=
  oa.mapM (fail := failure) (query_map := so.impl)

variable (so : SimOracle spec specₜ σ)

@[simp]
lemma simulateT_pure (x : α) : simulateT so (pure x) = pure x := mapM_pure _ _ x

@[simp]
lemma simulateT_failure : simulateT so (failure : OracleComp spec α) = StateT.lift failure := rfl

@[simp]
lemma simulateT_query_bind (q : OracleQuery spec α) (ob : α → OracleComp spec β) :
    simulateT so ((q : OracleComp spec α) >>= ob) = so.impl q >>= simulateT so ∘ ob := rfl

@[simp]
lemma simulateT_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    simulateT so (oa >>= ob) = simulateT so oa >>= (simulateT so ∘ ob) :=
  mapM_bind _ _ oa ob (λ _ ↦ rfl)

@[simp]
lemma simulateT_query (q : OracleQuery spec α) : simulateT so q = so.impl q :=
  mapM_query _ _ q

@[simp]
lemma simulateT_map (oa : OracleComp spec α) (f : α → β) :
    simulateT so (f <$> oa) = f <$> simulateT so oa :=
  mapM_map _ _ oa f (λ _ ↦ rfl)

@[simp]
lemma simulateT_seq (og : OracleComp spec (α → β)) (oa : OracleComp spec α) :
    simulateT so (og <*> oa) = simulateT so og <*> simulateT so oa :=
  mapM_seq _ _ og oa (λ _ ↦ rfl) (λ _ ↦ rfl)

@[simp]
lemma simulateT_ite (p : Prop) [Decidable p] (oa oa' : OracleComp spec α) :
    simulateT so (ite p oa oa') = ite p (simulateT so oa) (simulateT so oa') := by
  split_ifs <;> rfl

end simulateT

/-- `simulate so oa s` runs the computation `oa`, using the simulation oracle `so` to
answer any queries to the oracle, starting the simulation oracle's state with `s`. -/
@[reducible]
def simulate (so : spec →[σ]ₛₒ specₜ) (s : σ) (oa : OracleComp spec α) :
    OracleComp specₜ (α × σ) := (simulateT so oa).run s

lemma simulate_def (so : SimOracle spec specₜ σ) (s : σ) (oa : OracleComp spec α) :
    simulate so s oa = (simulateT so oa).run s := rfl

/-- Version of `simulate` that tosses out the oracle state at the end. -/
@[reducible]
def simulate' (so : spec →[σ]ₛₒ specₜ) (s : σ) (oa : OracleComp spec α) :
    OracleComp specₜ α := (simulateT so oa).run' s

lemma simulate'_def (so : spec →[σ]ₛₒ specₜ) (s : σ) (oa : OracleComp spec α) :
    simulate' so s oa = (simulateT so oa).run' s := rfl

section basic

variable {σ : Type u} (so : spec →[σ]ₛₒ specₜ)

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
  simp [simulate, simulateT_bind, StateT.run_bind]

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

variable {σ : Type u} (so : spec →[σ]ₛₒ specₜ)

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

section idem

variable {σ : Type u} (so : spec →[σ]ₛₒ spec)

/-- If `fst <$> so i (t, s)` has the same distribution as `query i t` for any state `s`,
Then `simulate' so` doesn't change the output distribution.
Stateless oracles are the most common example of this -/
lemma evalDist_simulate'_eq_evalDist [spec.FiniteRange]
    (h : ∀ i t s, (evalDist ((so.impl (query i t)).run' s)) =
      OptionT.lift (PMF.uniformOfFintype (spec.range i)))
    (s : σ) (oa : OracleComp spec α) : evalDist (simulate' so s oa) = evalDist oa := by
  revert s
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind i t oa hoa => exact (λ s ↦ by
      simp only [StateT.run'_eq] at h
      simp only [simulate'_bind, simulate_query, evalDist_bind, Function.comp_def, hoa,
        evalDist_query, ← h i t s, evalDist_map, PMF.bind_map, hoa, bind_map_left])
  | failure => intro s; rw [simulate'_failure]

end idem

section subsingleton

variable {σ : Type u} [Subsingleton σ] (so : spec →[σ]ₛₒ specₜ)

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

end OracleComp
