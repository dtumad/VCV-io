/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Constructions

/-!
# Coercions Between Computations With Additional Oracles

This file defines a `isSubSpec` relation for pairs of `oracleSpec` where one can be
thought of as an extension of the other with additional oracles.
The definition consists of a function from query inputs in the original oracle to a
computation using the new set of oracles, such that the result of the mapping
doesn't affect the underlying probability distribution on the oracle call.

We use the notation `spec ⊂ₒ spec'` to represent that one set of oracles is a subset of another,
where the non-inclusive subset symbol reflects that we avoid defining this instance reflexively.

We define the map to output a computation rather than a new set of oracle inputs in the new spec
to avoid type checking issues, as the `query` output type will not be definitionally equal
to the `query` output type in the original `oracle_spec`, causing issues in defining `has_coe`.
In practice the mapping will still usually output a `query` call,
and the equality between the underlying distributions is generally sufficient.

From this definition we construct a `Coe` instance to coerce a computation with one set of
oracles to one with a larger set of oracles, using the sub-spec inclusion functions
We show that this coercion has no effect on `support`, `eval_dist`, or `prob_event`.
-/

open OracleSpec OracleComp BigOperators

namespace OracleSpec

/-- Relation defining an inclusion of one set of oracles into another, where the mapping
doesn't affect the underlying probability distribution of the computation.
Informally, `sub_spec ⊂ₒ super_spec` means that for any query to an oracle of `sub_spec`,
it can be perfectly simulated by a computation using the oracles of `super_spec`. -/
class SubSpec (sub_spec : outParam OracleSpec) (super_spec : OracleSpec) where
  index_map : sub_spec.ι → super_spec.ι
  domain_map (i : sub_spec.ι) : sub_spec.domain i → super_spec.domain (index_map i)
  range_eq (i : sub_spec.ι) : sub_spec.range i = super_spec.range (index_map i)

infix : 50 " ⊂ₒ " => SubSpec

end OracleSpec

namespace OracleComp

/-- Coerce a computation using the replacement function defined in a `SubSpec` instance. -/
instance (sub_spec super_spec : OracleSpec) [h : sub_spec ⊂ₒ super_spec] (α : Type)  :
    Coe (OracleComp sub_spec α) (OracleComp super_spec α) where
      coe := λ oa ↦ simulate' (statelessOracle (λ i t ↦ h.range_eq i ▸
        query (h.index_map i) (h.domain_map i t))) oa ()

example {sub_spec super_spec : OracleSpec} [h : sub_spec ⊂ₒ super_spec]
    (oa : OracleComp sub_spec α) : OracleComp super_spec α := ↑oa

end OracleComp
