/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coercions.SubSpec

/-!
# Coercing Computations to Larger Oracle Sets

This file defines an append operation on `OracleSpec` to combine different sets of oracles.
We use `Sum` to combine the indexing sets, so this operation is "ordered"
in the sense that the two oracle sets correspond to `Sum.inl` and `Sum.inr`.
Note that this operation is never associative, as `Sum` is not associative

We also define a number of coercions involving append.
These instances allow an `OracleSpec` of the form `spec₁ ++ₒ ... ++ₒ spec₂`
to coerce to one of the form `spec'₁ ++ₒ ... ++ₒ spec'₂`, assuming that
the set of oracles in the first is a sub-sequence of the oracles in the second.
We also include associativity instances, so parenthisization of the sequence is irrelevant.

Note that this requires the ordering of oracles in each to match,
and so we generally adopt a standard ordering of `OracleSpec` for computations
in order to make this apply as often as possible. We specifically adopt the following convention:
  `{coin_oracle} ++ₒ {unif_spec} ++ₒ {random oracle} ++ₒ {adversary oracles} ++ₒ ...`,
where any of the individual parts may be ommited. The adversary oracles are for
things like a signing oracle in unforgeability experiments of a signature scheme.

TODO!: This is still not as powerful as what could be done in Lean3
** Maybe just manually add a ton of these, simp *should* mostly help that**

The typelcasses are applied in an order defined by specific priorities:
1. Try applying the associativity instance to remove parenthesization.
2. If both the subspec and superspec are an append, try to independently coerce both sides.
3. Try to coerce the subspec to the left side of the superspec append.
4. Try to coerce the subspec to the right side of the superspec append.
5. Try appending a single oracle to the left side of the subspec.
6. Try appending a single oracle to the right side of the subspec.
7. Try coercing the subspec to itself.
This ordering is chosen to both give a generally applicable instance tree,
and avoid an infinite typeclass search whether or not an instance exists.
-/

open OracleSpec OracleComp Sum

namespace OracleSpec

variable {ι₁ ι₂ ι₃ ι₄: Type} (spec₁ : OracleSpec ι₁) (spec₂ : OracleSpec ι₂)
  (spec₃ : OracleSpec ι₃) (spec₄ : OracleSpec ι₄) {α β γ : Type}

section instances

/-- Add additional oracles to the right side of the existing ones. -/
instance subSpec_append_left : spec₁ ⊂ₒ (spec₁ ++ₒ spec₂) where
  toFun := λ i t ↦ query (inl i) t
  evalDist_toFun' := by simp [append]

instance coe_append_left : Coe (OracleComp spec₁ α) (OracleComp (spec₁ ++ₒ spec₂) α) where
  coe := SubSpec.liftComp

/-- Add additional oracles to the left side of the exiting ones-/
instance subSpec_append_right : spec₂ ⊂ₒ (spec₁ ++ₒ spec₂) where
  toFun := λ i t ↦ query (inr i) t
  evalDist_toFun' := by simp [append]

instance coe_append_right : Coe (OracleComp spec₂ α) (OracleComp (spec₁ ++ₒ spec₂) α) where
  coe := SubSpec.liftComp

/-- Using a existing `subSpec`, also expand to even more additional oracles on the left. -/
instance subSpec_append_left_of_subSpec [h : spec₁ ⊂ₒ spec₃] : spec₁ ⊂ₒ (spec₂ ++ₒ spec₃) where
  toFun := λ i t ↦ SubSpec.liftComp (h.toFun i t)
  evalDist_toFun' := by simp [append]

-- instance coe_append_left_of_subSpec [h : spec₁ ⊂ₒ spec₃] :
--     Coe (OracleComp spec₁ α) (OracleComp (spec₂ ++ₒ spec₃) α) where
--   coe := SubSpec.liftComp

  /-- Using a existing `subSpec`, also expand to even more additional oracles on the right. -/
instance subSpec_append_right_of_subSpec [h : spec₁ ⊂ₒ spec₂] : spec₁ ⊂ₒ (spec₂ ++ₒ spec₃) where
  toFun := λ i t ↦ SubSpec.liftComp (h.toFun i t)
  evalDist_toFun' := by simp [append]

instance subSpec_left_append_left_append_of_subSpec [h : spec₁ ⊂ₒ spec₃] :
    spec₁ ++ₒ spec₂ ⊂ₒ spec₃ ++ₒ spec₂ where
  toFun := λ i t ↦ match i with
    | inl i => SubSpec.liftComp (h.toFun i t)
    | inr i => query (inr i) t
  evalDist_toFun' := by simp [append]

instance subSpec_right_append_right_append_of_subSpec [h : spec₂ ⊂ₒ spec₃] :
    spec₁ ++ₒ spec₂ ⊂ₒ spec₁ ++ₒ spec₃ where
  toFun := λ i t ↦ match i with
    | inl i => query (inl i) t
    | inr i => SubSpec.liftComp (h.toFun i t)
  evalDist_toFun' := by simp [append]

instance subSpec_assoc : spec₁ ++ₒ (spec₂ ++ₒ spec₃) ⊂ₒ spec₁ ++ₒ spec₂ ++ₒ spec₃ where
  toFun := λ i t ↦ match i with
    | inl i => query (inl (inl i)) t
    | inr (inl i) => query (inl (inr i)) t
    | inr (inr i) => query (inr i) t
  evalDist_toFun' := by simp [append]

instance : Coe (OracleComp (spec₁ ++ₒ (spec₂ ++ₒ spec₃)) α)
    (OracleComp (spec₁ ++ₒ spec₂ ++ₒ spec₃) α) where
  coe := SubSpec.liftComp

instance : Coe (OracleComp (spec₁ ++ₒ spec₂) α)
    (OracleComp (spec₁ ++ₒ (spec₂ ++ₒ spec₃)) α) where
  coe := SubSpec.liftComp

instance : Coe (OracleComp (spec₁ ++ₒ spec₃) α)
    (OracleComp ((spec₁ ++ₒ spec₂) ++ₒ spec₃) α) where
  coe := SubSpec.liftComp

end instances

end OracleSpec

section tests

set_option linter.unusedVariables false

-- This set of examples serves as sort of a "unit test" for the coercions above
variable (α ι₁ ι₂ ι₃ ι₄ ι₅ ι₆ : Type)
  (spec₁ : OracleSpec ι₁) (spec₂ : OracleSpec ι₂)
  (spec₃ : OracleSpec ι₃) (spec₄ : OracleSpec ι₄)
  (coeSpec : OracleSpec ι₅) (coeSuperSpec : OracleSpec ι₆)
  [coeSpec ⊂ₒ coeSuperSpec]

-- coerce a single `coin_spec` and then append extra oracles
example (oa : OracleComp coeSpec α) :
  OracleComp (coeSuperSpec ++ₒ spec₂ ++ₒ spec₃) α := SubSpec.liftComp oa
example (oa : OracleComp coeSpec α) :
  OracleComp (spec₁ ++ₒ coeSuperSpec ++ₒ spec₂) α := SubSpec.liftComp oa
example (oa : OracleComp coeSpec α) :
  OracleComp (spec₁ ++ₒ spec₂ ++ₒ coeSuperSpec) α := SubSpec.liftComp oa

-- coerce left side of append and then append on additional oracles
example (oa : OracleComp (coeSpec ++ₒ spec₁) α) :
  OracleComp (coeSuperSpec ++ₒ spec₁ ++ₒ spec₂) α := SubSpec.liftComp oa
example (oa : OracleComp (coeSpec ++ₒ spec₁) α) :
  OracleComp (coeSuperSpec ++ₒ spec₂ ++ₒ spec₁) α := SubSpec.liftComp oa
example (oa : OracleComp (coeSpec ++ₒ spec₁) α) :
  OracleComp (spec₂ ++ₒ coeSuperSpec ++ₒ spec₁) α := SubSpec.liftComp oa

-- coerce right side of append and then append on additional oracles
example (oa : OracleComp (spec₁ ++ₒ coeSpec) α) :
  OracleComp (spec₁ ++ₒ coeSuperSpec ++ₒ spec₂) α := SubSpec.liftComp oa
-- example (oa : OracleComp (spec₁ ++ₒ coeSpec) α) :
--   OracleComp (spec₁ ++ₒ spec₂ ++ₒ coeSuperSpec) α := SubSpec.liftComp oa
-- example (oa : OracleComp (spec₁ ++ₒ coeSpec) α) :
--   OracleComp (spec₂ ++ₒ spec₁ ++ₒ coeSuperSpec) α := SubSpec.liftComp oa

-- -- coerce an inside part while also applying associativity
-- example (oa : OracleComp (spec₁ ++ₒ (spec₂ ++ₒ coeSpec)) α) :
--   OracleComp (spec₁ ++ₒ spec₂ ++ₒ coeSuperSpec) α := SubSpec.liftComp oa
-- example (oa : OracleComp (spec₁ ++ₒ (coeSpec ++ₒ spec₂)) α) :
--   OracleComp (spec₁ ++ₒ coeSuperSpec ++ₒ spec₂) α := SubSpec.liftComp oa
-- example (oa : OracleComp (coeSpec ++ₒ (spec₁ ++ₒ spec₂)) α) :
--   OracleComp (coeSuperSpec ++ₒ spec₁ ++ₒ spec₂) α := SubSpec.liftComp oa

-- coerce two oracles up to four oracles
example (oa : OracleComp (spec₁ ++ₒ spec₂) α) :
  OracleComp (spec₁ ++ₒ spec₂ ++ₒ spec₃ ++ₒ spec₄) α := SubSpec.liftComp oa
example (oa : OracleComp (spec₁ ++ₒ spec₃) α) :
  OracleComp (spec₁ ++ₒ spec₂ ++ₒ spec₃ ++ₒ spec₄) α := SubSpec.liftComp oa
example (oa : OracleComp (spec₁ ++ₒ spec₄) α) :
  OracleComp (spec₁ ++ₒ spec₂ ++ₒ spec₃ ++ₒ spec₄) α := SubSpec.liftComp oa
example (oa : OracleComp (spec₂ ++ₒ spec₃) α) :
  OracleComp (spec₁ ++ₒ spec₂ ++ₒ spec₃ ++ₒ spec₄) α := SubSpec.liftComp oa
example (oa : OracleComp (spec₂ ++ₒ spec₄) α) :
  OracleComp (spec₁ ++ₒ spec₂ ++ₒ spec₃ ++ₒ spec₄) α := SubSpec.liftComp oa
example (oa : OracleComp (spec₃ ++ₒ spec₄) α) :
  OracleComp (spec₁ ++ₒ spec₂ ++ₒ spec₃ ++ₒ spec₄) α := SubSpec.liftComp oa

-- coerce threee oracles up to four oracles
example (oa : OracleComp (spec₁ ++ₒ spec₂ ++ₒ spec₃) α) :
  OracleComp (spec₁ ++ₒ spec₂ ++ₒ spec₃ ++ₒ spec₄) α := SubSpec.liftComp oa
example (oa : OracleComp (spec₁ ++ₒ spec₂ ++ₒ spec₄) α) :
  OracleComp (spec₁ ++ₒ spec₂ ++ₒ spec₃ ++ₒ spec₄) α := SubSpec.liftComp oa
example (oa : OracleComp (spec₁ ++ₒ spec₃ ++ₒ spec₄) α) :
  OracleComp (spec₁ ++ₒ spec₂ ++ₒ spec₃ ++ₒ spec₄) α := SubSpec.liftComp oa
example (oa : OracleComp (spec₂ ++ₒ spec₃ ++ₒ spec₄) α) :
  OracleComp (spec₁ ++ₒ spec₂ ++ₒ spec₃ ++ₒ spec₄) α := SubSpec.liftComp oa

-- -- four oracles with associativity and internal coercion
-- example (oa : OracleComp ((coeSpec ++ₒ spec₂) ++ₒ (spec₃ ++ₒ spec₄)) α) :
--   OracleComp (coeSuperSpec ++ₒ spec₂ ++ₒ spec₃ ++ₒ spec₄) α := SubSpec.liftComp oa
-- example (oa : OracleComp ((spec₁ ++ₒ spec₂) ++ₒ (coeSpec ++ₒ spec₄)) α) :
--   OracleComp (spec₁ ++ₒ spec₂ ++ₒ coeSuperSpec ++ₒ spec₄) α := SubSpec.liftComp oa
-- example (oa : OracleComp ((spec₁ ++ₒ coeSpec) ++ₒ (spec₃ ++ₒ spec₄)) α) :
--   OracleComp (spec₁ ++ₒ coeSuperSpec ++ₒ spec₃ ++ₒ spec₄) α := SubSpec.liftComp oa
-- example (oa : OracleComp ((spec₁ ++ₒ spec₂) ++ₒ (spec₃ ++ₒ coeSuperSpec)) α) :
--   OracleComp (spec₁ ++ₒ spec₂ ++ₒ spec₃ ++ₒ coeSuperSpec) α := SubSpec.liftComp oa

/-- coercion makes it possible to mix computations on individual oracles -/
example : OracleComp (unifSpec ++ₒ spec₁) Bool := do
  let n : Fin 315 ←$[0..314]; let m : Fin 315 ←$[0..314]
  if n = m then return true else coin

end tests
