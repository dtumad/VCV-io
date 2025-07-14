/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.HasSupportM
import VCVio.OracleComp.OracleComp

/-!
# Output Distribution of Computations

This file defines a `HasEvalDist` for `OracleComp`, assuming uniform outputs of computations.
-/

open OracleSpec Option ENNReal BigOperators

universe u v w

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {ι' : Type v} {spec' : OracleSpec ι'}
  {α β γ : Type w} [spec.FiniteRange] [spec'.FiniteRange]

/-- Create an arbitrary `HasEvalDist` instance from an embedding of queries into `SPMF`. -/
protected noncomputable def hasEvalDist_of_mapM
    (query_dist : {α : Type _} → OracleQuery spec α → SPMF α) : HasEvalDist (OracleComp spec) where
  evalDist := OracleComp.mapM query_dist
  evalDist_pure x := rfl
  evalDist_bind oa ob := by rw [mapM_bind]

/-- The standard evaluation distribution on `OracleComp` given by mapping queries to a uniform
output distribution. In the case of `ProbComp` this is exactly the distribution coming from
each uniform selection responding uniformly. -/
noncomputable instance [spec.FiniteRange] : HasEvalDist (OracleComp spec) :=
  OracleComp.hasEvalDist_of_mapM (fun | query i _ => PMF.uniformOfFintype (spec.range i))

end OracleComp
