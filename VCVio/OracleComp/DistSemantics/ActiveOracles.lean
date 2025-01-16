/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.OracleComp

/-!
# Oracles Used by a Computation

This file defines a function `OracleComp.activeOracles` that
returns the set of oracle indices that can possibly be called by a computation.
Works by just traversing the entire possible execution space,
so this really shouldn't be used in practice.
However it can be useful in proving certain lemmas about existence of certain reductions.
-/

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- Given that the indexing set has decidable equality, return a finite set of all
the indices that can ever be used in a query by a computation,
by just traversing all possible execution paths. -/
def activeOracles [spec.FiniteRange] [DecidableEq ι] (oa : OracleComp spec α) : Finset ι := by
  induction oa using OracleComp.construct' with
  | query_bind i _ _ r => exact insert i (Finset.univ.biUnion r)
  | _ => exact ∅

end OracleComp
