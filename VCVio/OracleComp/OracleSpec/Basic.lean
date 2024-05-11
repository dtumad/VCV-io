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
-/

/-- A structure to represents a specification of oracles available to a computation.
The available oracles are all indexed by some (potentially infinite) indexing set `ι`.
For each `i : ι`, `domain i` and `range i` are the input and output types of the oracle. -/
structure OracleSpec (ι : Type) where
  domain : ι → Type
  range : ι → Type
  domain_decidableEq' : ∀ i, DecidableEq $ domain i
  range_decidableEq' : ∀ i, DecidableEq $ range i
  range_inhabited' : ∀ i, Inhabited $ range i
  range_fintype' : ∀ i, Fintype $ range i

namespace OracleSpec

variable {ι : Type} {spec : OracleSpec ι} (i : ι)

-- instance ι_decidableEq : DecidableEq ι := spec.ι_decidableEq'
instance domain_decidableEq : DecidableEq (spec.domain i) := spec.domain_decidableEq' i
instance range_decidableEq : DecidableEq (spec.range i) := spec.range_decidableEq' i
instance range_inhabited : Inhabited (spec.range i) := spec.range_inhabited' i
instance range_fintype : Fintype (spec.range i) := spec.range_fintype' i

@[simp] lemma card_range_ne_zero (i : ι) :
  Fintype.card (spec.range i) ≠ 0 := Fintype.card_ne_zero

end OracleSpec

/-- Access to no oracles, represented by an empty indexing set.
We take the domain and range to be `Unit` (rather than e.g. `empty.elim i`),
which often gives better behavior for proofs even though the oracle is never called. -/
@[simps] def emptySpec : OracleSpec Empty where
  domain := λ _ ↦ Unit
  range := λ _ ↦ Unit
  range_inhabited' := inferInstance
  domain_decidableEq' := inferInstance
  range_decidableEq' := inferInstance
  range_fintype' := inferInstance

notation "[]ₒ" => emptySpec

instance (i : Empty) : Unique ([]ₒ.domain i) := PUnit.unique
instance (i : Empty) : Unique ([]ₒ.range i) := PUnit.unique

instance {ι : Type} [DecidableEq ι] : Inhabited (OracleSpec ι) :=
  ⟨{
    domain := λ _ ↦ Unit
    range := λ _ ↦ Unit
    domain_decidableEq' := inferInstance
    range_decidableEq' := inferInstance
    range_inhabited' := inferInstance
    range_fintype' := inferInstance
  }⟩

/-- `T →ₒ U` represents a single oracle, with domain `T` and range `U`. -/
@[inline, reducible] def singletonSpec (T U : Type) [Inhabited U] [DecidableEq T]
    [DecidableEq U] [Fintype U] : OracleSpec Unit where
  domain := λ _ ↦ T
  range := λ _ ↦ U
  range_inhabited' := inferInstance
  domain_decidableEq' := inferInstance
  range_decidableEq' := inferInstance
  range_fintype' := inferInstance

infixl : 25 " →ₒ " => singletonSpec

-- instance (T U : Type) [Inhabited U] [DecidableEq T]
--   [DecidableEq U] [Fintype U] : Unique (T →ₒ U).ι := PUnit.unique

/-- A coin flipping oracle produces a random `Bool` with no meaningful input.

NOTE: debate on whether inlining this is good -/
@[inline, reducible] def coinSpec : OracleSpec Unit := Unit →ₒ Bool

/-- Access to oracles for uniformly selecting from `Fin (n + 1)` for arbitrary `n : ℕ`.
By adding `1` to the index we avoid selection from the empty type `Fin 0 ≃ empty`.

NOTE: debate on whether inlining this is good -/
@[inline, reducible] def unifSpec : OracleSpec ℕ where
  -- ι := ℕ
  domain := λ _ ↦ Unit
  range := λ n ↦ Fin (n + 1)
  range_inhabited' := inferInstance
  -- ι_decidableEq' := inferInstance
  domain_decidableEq' := inferInstance
  range_decidableEq' := inferInstance
  range_fintype' := inferInstance

instance (i : ℕ) : Unique (unifSpec.domain i) := PUnit.unique
