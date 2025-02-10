/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Simulate

/-!
# Seeding Results of Queries

This file defines a simulation oracle `seededOracle` for pre-choosing the responses to queries.
The internal state is a list of seeded values for each oracle, and the simulation will use these
when possible, defaulting back to the original behavior if the seed doesn't have enough values.

We also clear the remaining seed if any single oracle fails to have enough seed values.
This simplifies a number of lemmas by making the computation revert to its original behavior.
-/

open OracleComp OracleSpec BigOperators

variable {ι : Type} {spec : OracleSpec ι}

namespace OracleSpec

/-- Type to represent a store of seed values to use in a computation, represented as a function.
Updates to individual seed lists are performed via continuation passing. -/
def QuerySeed (spec : OracleSpec ι) : Type :=
  (i : ι) → List (spec.range i)

namespace QuerySeed

instance : DFunLike (QuerySeed spec) ι (λ i ↦ List (spec.range i)) where
  coe := λ seed ↦ seed
  coe_injective' := Function.injective_id

@[ext]
protected lemma ext (seed₁ seed₂ : QuerySeed spec) (h : ∀ i, seed₁ i = seed₂ i) : seed₁ = seed₂ :=
    DFunLike.ext seed₁ seed₂ h

-- @[simp] lemma DfunLike_coe_apply

@[simp] instance : EmptyCollection (QuerySeed spec) := ⟨λ _ ↦ []⟩

def update [DecidableEq ι] (seed : QuerySeed spec) (i : ι)
    (xs : List (spec.range i)) : QuerySeed spec :=
  Function.update seed i xs

section addValues

/-- Add a list of values to the query seed.-/
def addValues [DecidableEq ι] {i : ι}
    (us : List (spec.range i)) (seed : QuerySeed spec) : QuerySeed spec :=
  Function.update seed i (seed i ++ us)

variable [DecidableEq ι] {i : ι} (seed : QuerySeed spec) (us : List (spec.range i))

@[simp]
lemma addValues_apply (j : ι) : seed.addValues us j =
    Function.update seed i (seed i ++ us) j := rfl

@[simp]
lemma addValues_nil {i : ι} (seed : QuerySeed spec) : seed.addValues (i := i) [] = seed := by
  simp only [addValues, List.append_nil, Function.update_eq_self]

/-- Add a single value into the seed, by adding a singleton list -/
abbrev addValue (seed : QuerySeed spec) (i : ι) (u : spec.range i) : QuerySeed spec :=
  seed.addValues [u]

end addValues

section takeAtIndex

/-- Take only the first `n` values of the seed at index `i`. -/
def takeAtIndex [DecidableEq ι] (seed : QuerySeed spec) (i : ι) (n : ℕ) : QuerySeed spec :=
  Function.update seed i ((seed i).take n)

variable [DecidableEq ι] (seed : QuerySeed spec) (i : ι) (n : ℕ)

@[simp]
lemma takeAtIndex_apply (j : ι) : seed.takeAtIndex i n j =
    (Function.update seed i ((seed i).take n) j) := rfl

@[simp]
lemma takeAtIndex_addValues (seed : QuerySeed spec) {i : ι} (n : ℕ) (xs : List (spec.range i)) :
    (seed.addValues xs).takeAtIndex i n = if n ≤ (seed i).length
      then seed.takeAtIndex i n else seed.addValues (xs.take (n - (seed i).length)) := by
  refine funext (λ j ↦ ?_)
  by_cases hj : j = i
  · induction hj
    split_ifs with hn
    · simp [hn]
    · suffices List.take n (seed j ++ xs) = seed j ++ List.take (n - (seed j).length) xs
      by simpa using this
      rw [List.take_append_eq_append_take]
      simpa using le_of_not_le hn
  · split_ifs with _ <;> simp [hj]

-- @[simp]
-- lemma addValues_takeAtIndex (seed : QuerySeed spec) {i : ι} (xs : List (spec.range i)) (n : ℕ) :
--     (seed.takeAtIndex i n).addValues xs =

@[simp]
lemma takeAtIndex_length (seed : QuerySeed spec) (i : ι) :
    seed.takeAtIndex i (seed i).length = seed := funext (λ j ↦ by simp)

lemma eq_takeAtIndex_length_iff (seed seed' : QuerySeed spec) (i : ι) :
    seed = seed'.takeAtIndex i (seed i).length ↔
      seed' = seed.addValues ((seed' i).drop (seed i).length) := by
  refine ⟨λ h ↦ QuerySeed.ext _ _ (λ j ↦ ?_), λ h ↦ ?_⟩
  · by_cases hj : j = i
    · induction hj
      rw [h]
      suffices (seed j).length ≤ (seed' j).length
      by simp [this]
      simpa using congr_arg List.length (congr_fun h j)
    · rw [h]
      simp [hj]
  · rw [h]
    simp

end takeAtIndex

-- def nextSeed [DecidableEq ι] {α : Type} :
--     (q : OracleQuery spec α) → StateT (QuerySeed spec) (OracleComp spec) α
--   | query i t => do
--     let seed ← get
--     return List.get?
--     match (← get) i with
--       | u :: us => return (u, Function.update seed i us)
--       | [] => failure

lemma eq_addValues_iff [DecidableEq ι] (seed seed' : QuerySeed spec)
    {i : ι} (xs : List (spec.range i)) :
    seed = seed'.addValues xs ↔ seed' = seed.takeAtIndex i (seed' i).length ∧
      xs = (seed i).drop (seed' i).length := by
  refine ⟨λ h ↦ ?_, λ ⟨h1, h2⟩ ↦ ?_⟩
  · simp [h]
  · rw [h1, h2]
    refine funext (λ j ↦ ?_)
    by_cases hj : j = i
    · induction hj; simp
    · simp [hj]

lemma addValues_eq_iff [DecidableEq ι] (seed seed' : QuerySeed spec)
    {i : ι} (xs : List (spec.range i)) :
    seed.addValues xs = seed' ↔ seed = seed'.takeAtIndex i (seed i).length ∧
      xs = (seed' i).drop (seed i).length :=
  eq_comm.trans (eq_addValues_iff seed' seed xs)

end QuerySeed

end OracleSpec

-- `ReaderT` might not make sense here, `adapt` is basically used as `StateT.modify`.
def seededOracle' [DecidableEq ι] :
    SimOracle' spec spec (ReaderT (QuerySeed spec)) where
  impl | query i t => do match (← read) i with
    | u :: us => ReaderT.adapt (QuerySeed.update · i us) (return u)
    | [] => query i t -- Don't actually drop rest of the seed this way

def seededOracle'' [DecidableEq ι] :
    QueryImpl spec (ReaderT (QuerySeed spec) (OracleComp spec)) where
  impl | query i t => do match (← read) i with
    | u :: us => ReaderT.adapt (QuerySeed.update · i us) (return u)
    | [] => query i t

def seededOracle [DecidableEq ι] : SimOracle spec spec (QuerySeed spec) where
  impl | query i t => do
    match (← get) i with
    | u :: us => modify (QuerySeed.update · i us); return u
    | [] => set (∅ : QuerySeed spec); query i t

namespace seededOracle

end seededOracle
