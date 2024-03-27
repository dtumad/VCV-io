/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.OracleSpec.SubSpec

/-!
# Appending Sets of Oracles

This file defines an append operation on `OracleSpec` to combine different sets of oracles.
We use `Sum` to combine the indexing sets, so this operation is "ordered"
in the sense that the two oracle sets correspond to `Sum.inl` and `Sum.inr`.
Note that this operation is never associative, as `Sum` is not associative

We also define a number of coercions involving append.
These instances allow an `OracleSpec` of the form `spec₁ ++ ... ++ spec₂`
to coerce to one of the form `spec'₁ ++ ... ++ spec'₂`, assuming that
the set of oracles in the first is a sub-sequence of the oracles in the second.
We also include associativity instances, so parenthisization of the sequence is irrelevant.

Note that this requires the ordering of oracles in each to match,
and so we generally adopt a standard ordering of `OracleSpec` for computations
in order to make this apply as often as possible. We specifically adopt the following convention:
  `{coin_oracle} ++ {unif_spec} ++ {random oracle} ++ {adversary oracles} ++ ...`,
where any of the individual parts may be ommited. The adversary oracles are for
things like a signing oracle in unforgeability experiments of a signature scheme.

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

namespace OracleSpec

/-- `spec₁ ++ spec₂` combines the two sets of oracles disjointly using `Sum` for the indexing set.
`Sum.inl i` is a query to oracle `i` of `spec`, and `Sum.inr i` for oracle `i` of `spec'`. -/
@[simps] instance : Append OracleSpec where
  append := λ spec₁ spec₂ ↦
  { ι := spec₁.ι ⊕ spec₂.ι,
    domain := λ i ↦ match i with
      | Sum.inl i => spec₁.domain i
      | Sum.inr i => spec₂.domain i,
    range := λ i ↦ match i with
      | Sum.inl i => spec₁.range i
      | Sum.inr i => spec₂.range i,
    range_inhabited' := λ i ↦ Sum.recOn i spec₁.range_inhabited spec₂.range_inhabited,
    ι_decidableEq' := instDecidableEqSum,
    domain_decidableEq' := λ i ↦ Sum.recOn i spec₁.domain_decidableEq spec₂.domain_decidableEq,
    range_decidableEq' := λ i ↦ Sum.recOn i spec₁.range_decidableEq spec₂.range_decidableEq,
    range_fintype' := λ i ↦ Sum.recOn i spec₁.range_fintype spec₂.range_fintype }

-- instance subSpec_append_left (spec₁ spec₂) : spec₂ ⊂ₒ (spec₁ ++ spec₂)

end OracleSpec