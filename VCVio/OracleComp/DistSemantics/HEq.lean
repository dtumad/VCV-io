/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.EvalDist

/-!
# Hetorogeneous Equality Between Computations and Associated Probability

Lemmas about `HEq` related to `evalDist` and computations in general.
-/

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

-- lemma output_type_eq_of_heq {α β : Type} {oa : OracleComp spec α} {ob : OracleComp spec β}
--     (h : HEq oa ob) : α = β := by
--   sorry

-- lemma support_heq_of_heq {α β : Type} {oa : OracleComp spec α} {ob : OracleComp spec β}
--     (h' : HEq oa ob) : HEq oa.support ob.support := by
--   sorry
