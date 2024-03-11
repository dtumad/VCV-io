/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import «VCV-io».OracleComp.OracleSpec

inductive OracleComp (spec : OracleSpec) : Type → Type 1
  | pure' (α : Type) (a : α) : OracleComp spec α
  | query_bind' (i : spec.ι) (t : spec.domain i) (α : Type)
      (oa : spec.range i → OracleComp spec α) : OracleComp spec α
