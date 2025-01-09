/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coercions.Append

/-!
# Using Simulation Oracles in Sequence

This file defines a function `untilSwap` to combine two `SimOracle`,
first answering queries to the first oracle and then answering queries to the second,
under the assumption that the swap happens only once.
Takes in a function that updates the state from the first to the second.

This can be usefull when sequencing two computations when you want to avoid exploding
the size of the state type (as `SimOracle.append` would do) it makes it possible to use
a sum type instead of a product type.

NOTE: this could be generalized to go back and forth more generally,
but seems unneeded until we have an actual use case.
-/

open OracleSpec OracleComp Sum Prod

namespace SimOracle

variable {ι₁ ι₂ ι : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {spec : OracleSpec ι} {σ₁ σ₂ α β γ : Type}

/-- Given two simulation oracles `so` and `so'` with the same target `spec : OracleSpec ι`,
construct a simulation oracle that uses `so` for queries to the first and then starts using `so'`
after the first query to the second. Defined to fail if it recieves queries to the first
after recieving queries to the first.

The function `f` is used to move to the second state type after the swap.
NOTE: `f` could eventually be an `OracleComp spec σ₂`, but no clear use case,
maybe if this where a two way thing then it could be used for failures. -/
def untilSwap (so : spec₁ →[σ₁]ₛₒ spec) (so' : spec₂ →[σ₂]ₛₒ spec)
    (f : σ₁ → σ₂) : spec₁ ++ₒ spec₂ →[σ₁ ⊕ σ₂]ₛₒ spec where impl
  | query (inl i) t, inl s => map id inl <$> so.impl (query i t) s
  | query (inr i) t, inl s => map id inr <$> so'.impl (query i t) (f s)
  | query (inr i) t, inr s => map id inr <$> so'.impl (query i t) s
  | _, _ => failure -- swapped back to first from second

variable (so : spec₁ →[σ₁]ₛₒ spec) (so' : spec₂ →[σ₂]ₛₒ spec) (f : σ₁ → σ₂)

/-- Simulating a computation using only `spec₁` bound to a computation using only `spec₂`
(using the natural `OracleSpec.append` coercions) with `SimOracle.untilSwap so so' f`
is the same as simulating the first with `so` and then simulating the second with `so'`,
using the function `f` to bridge the gap between the two states. -/
lemma simulate_untilSwap_coe_bind_coe (oa : OracleComp spec₁ α)
    (ob : α → OracleComp spec₂ β) (s : σ₁) :
    simulate (so.untilSwap so' f) (inl s) (↑oa >>= λ x ↦ ↑(ob x)) = (do
      let (x, s') ← simulate so s oa
      Prod.map id inr <$> simulate so' (f s') (ob x)) :=
  sorry

/-- Version of `simulate_untilSwap_coe_bind_coe` when the final state doesn't matter. -/
lemma simulate'_untilSwap_coe_bind_coe (oa : OracleComp spec₁ α)
    (ob : α → OracleComp spec₂ β) (s : σ₁) :
    simulate' (so.untilSwap so' f) (inl s) (↑oa >>= λ x ↦ ↑(ob x)) = (do
      let (x, s') ← simulate so s oa
      simulate' so' (f s') (ob x)) :=
  sorry


end SimOracle
