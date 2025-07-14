/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.HasFinEvalDist
import VCVio.OracleComp.OracleComp

/-!
# Output Distribution of Computations

This file defines a `HasEvalDist` for `OracleComp`, assuming uniform outputs of computations.
-/

open OracleSpec Option ENNReal BigOperators

universe u v w

namespace OracleComp

variable {spec : OracleSpec} {spec' : OracleSpec}
  {α β γ : Type w} [spec.Fintype] [spec'.Fintype]


-- /-- Create an arbitrary `HasEvalDist` instance from an embedding of queries into `SPMF`. -/
-- protected noncomputable def hasEvalDist_of_mapM
--     (query_dist : {α : Type _} → OracleQuery spec α → SPMF α) :
--     HasEvalDist (OracleComp spec) where
--   evalDist := sorry -- OracleComp.mapM query_dist
  -- evalDist_pure x := rfl
  -- evalDist_bind oa ob := by rw [mapM_bind]

noncomputable instance [spec.Fintype] : HasSupportM (OracleComp spec) :=
  sorry --OracleComp.hasEvalDist_of_mapM (fun | query i _ => PMF.uniformOfFintype (spec.range i))

/-- The standard evaluation distribution on `OracleComp` given by mapping queries to a uniform
output distribution. In the case of `ProbComp` this is exactly the distribution coming from
each uniform selection responding uniformly. -/
noncomputable instance [spec.Fintype] : HasEvalDist (OracleComp spec) :=
  sorry --OracleComp.hasEvalDist_of_mapM (fun | query i _ => PMF.uniformOfFintype (spec.range i))

end OracleComp
