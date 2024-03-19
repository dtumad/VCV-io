/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Data.Fintype.Card

/-!
# Specifications of Available Oracles

This file defines a type `OracleSpec` to represent a set of available oracles.
The available oracles are all indexed by some (potentially infinite) indexing set `ι`,
and for each index `i` a pair of types `domain i` and `range i`.

We also bundle a number of typeclasses into the defintion.
Specifically these are necessary to give most of the denotational semantics.
Seperating them out would require making some typeclass for "computable" specs.

We also define a number of basic oracle constructions:
* `∅`: Access to no oracles
* `T →ₒ U`: Access to a single oracle with given input and output
* `coinSpec`: A single oracle for flipping a coin
* `unifSpec`: A family of oracles for selecting from `[0..n]` for any `n`
* `spec ++ spec'`: Access to oracles in either of the two specs
-/

/-- A structure to represents a specification of oracles available to a computation.
The available oracles are all indexed by some (potentially infinite) indexing set `ι`.
For each `i : ι`, `domain i` and `range i` are the input and output types of the oracle. -/
structure OracleSpec where
  ι : Type
  domain : ι → Type
  range : ι → Type
  ι_decidableEq' : DecidableEq ι
  domain_decidableEq' : ∀ i, DecidableEq $ domain i
  range_decidableEq' : ∀ i, DecidableEq $ range i
  range_inhabited' : ∀ i, Inhabited $ range i
  range_fintype' : ∀ i, Fintype $ range i

namespace OracleSpec

variable {spec : OracleSpec} (i : spec.ι)

instance ι_decidableEq : DecidableEq spec.ι := spec.ι_decidableEq'
instance domain_decidableEq : DecidableEq (spec.domain i) := spec.domain_decidableEq' i
instance range_decidableEq : DecidableEq (spec.range i) := spec.range_decidableEq' i
instance range_inhabited : Inhabited (spec.range i) := spec.range_inhabited' i
instance range_fintype : Fintype (spec.range i) := spec.range_fintype' i

@[simp] lemma card_range_ne_zero {spec : OracleSpec} (i : spec.ι) :
  Fintype.card (spec.range i) ≠ 0 := Fintype.card_ne_zero

end OracleSpec

/-- Access to no oracles, represented by an empty indexing set.
We take the domain and range to be `Unit` (rather than e.g. `empty.elim i`),
which often gives better behavior for proofs even though the oracle is never called. -/
@[simps] def emptySpec : OracleSpec where
  ι := Empty
  domain := λ _ ↦ Unit
  range := λ _ ↦ Unit
  range_inhabited' := inferInstance
  ι_decidableEq' := inferInstance
  domain_decidableEq' := inferInstance
  range_decidableEq' := inferInstance
  range_fintype' := inferInstance

instance : IsEmpty (emptySpec.ι) := instIsEmptyEmpty
instance (i : emptySpec.ι) : Unique (emptySpec.domain i) := PUnit.unique
instance (i : emptySpec.ι) : Unique (emptySpec.range i) := PUnit.unique

instance : EmptyCollection OracleSpec := ⟨emptySpec⟩
instance : Inhabited OracleSpec := ⟨∅⟩

/-- `T →ₒ U` represents a single oracle, with domain `T` and range `U`. -/
@[simps] def singletonSpec (T U : Type) [Inhabited U] [DecidableEq T]
  [DecidableEq U] [Fintype U] : OracleSpec where
  ι := Unit
  domain := λ _ ↦ T
  range := λ _ ↦ U
  range_inhabited' := inferInstance
  ι_decidableEq' := inferInstance
  domain_decidableEq' := inferInstance
  range_decidableEq' := inferInstance
  range_fintype' := inferInstance

infixl : 25 " →ₒ " => singletonSpec

instance (T U : Type) [Inhabited U] [DecidableEq T]
  [DecidableEq U] [Fintype U] : Unique (T →ₒ U).ι := PUnit.unique

/-- A coin flipping oracle produces a random `Bool` with no meaningful input.

NOTE: debate on whether inlining this is good -/
@[inline, reducible] def coinSpec : OracleSpec := Unit →ₒ Bool

/-- Access to oracles for uniformly selecting from `Fin (n + 1)` for arbitrary `n : ℕ`.
By adding `1` to the index we avoid selection from the empty type `Fin 0 ≃ empty`.

NOTE: debate on whether inlining this is good -/
@[simps, inline, reducible] def unifSpec : OracleSpec where
  ι := ℕ
  domain := λ _ ↦ Unit
  range := λ n ↦ Fin (n + 1)
  range_inhabited' := inferInstance
  ι_decidableEq' := inferInstance
  domain_decidableEq' := inferInstance
  range_decidableEq' := inferInstance
  range_fintype' := inferInstance

instance (i : unifSpec.ι) : Unique (unifSpec.domain i) := PUnit.unique

/-- `spec ++ spec'` combines the two sets of oracles disjointly using `Sum` for the indexing set.
`Sum.inl i` is a query to oracle `i` of `spec`, and `Sum.inr i` for oracle `i` of `spec'`. -/
@[simps] instance : Append OracleSpec where
  append := λ spec spec' ↦
  { ι := spec.ι ⊕ spec'.ι,
    domain := λ i ↦ match i with
      | Sum.inl i => spec.domain i
      | Sum.inr i => spec'.domain i,
    range := λ i ↦ match i with
      | Sum.inl i => spec.range i
      | Sum.inr i => spec'.range i,
    range_inhabited' := λ i ↦ Sum.recOn i spec.range_inhabited spec'.range_inhabited,
    ι_decidableEq' := instDecidableEqSum,
    domain_decidableEq' := λ i ↦ Sum.recOn i spec.domain_decidableEq spec'.domain_decidableEq,
    range_decidableEq' := λ i ↦ Sum.recOn i spec.range_decidableEq spec'.range_decidableEq,
    range_fintype' := λ i ↦ Sum.recOn i spec.range_fintype spec'.range_fintype }
