/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import «VCV-io».OracleComp.OracleComp

namespace OracleComp

def support {α : Type} : OracleComp spec α → Set α
| pure' _ x => {x}
| query_bind' _ _ _ oa => ⋃ u, (oa u).support

def finSupport {α : Type} [DecidableEq α] : OracleComp spec α → Finset α
| pure' _ x => {x}
| query_bind' _ _ _ oa => Finset.biUnion Finset.univ (λ u ↦ (oa u).finSupport)

variable {spec : OracleSpec} {α β : Type}

@[simp] lemma support_pure (x : α) : (pure x : OracleComp spec α).support = {x} := rfl

@[simp] lemma finSupport_pure (x : α) [DecidableEq α] :
  (pure x : OracleComp spec α).finSupport = {x} := rfl

@[simp] lemma support_query (i : spec.ι) (t : spec.domain i) :
  (query i t).support = Set.univ :=
by simpa only [query_def, support] using Set.iUnion_of_singleton (spec.range i)

@[simp] lemma finSupport_query (i : spec.ι) (t : spec.domain i) :
  (query i t).finSupport = Finset.univ :=
by simpa only [query_def, finSupport] using Finset.biUnion_singleton_eq_self

@[simp] lemma support_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
  (oa >>= ob).support = ⋃ x ∈ oa.support, (ob x).support :=
by induction oa using OracleComp.induction_on with
| h_pure _ => simp
| h_query_bind i t h => simpa [bind_assoc, ← query_bind'_eq_query_bind, support, h]
    using Set.iUnion_comm _

@[simp] lemma finSupport_bind  (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
  [DecidableEq α] → [DecidableEq β] →
    (oa >>= ob).finSupport = oa.finSupport.biUnion (λ x ↦ (ob x).finSupport) :=
by induction oa using OracleComp.induction_on with
| h_pure _ => simp
| h_query_bind i t h =>
    intros hα hβ; apply Finset.coe_inj.1
    simpa [bind_assoc, ← query_bind'_eq_query_bind, finSupport, h] using Set.iUnion_comm _

@[simp] lemma coe_finSupport : {α : Type} → [DecidableEq α] →
  (oa : OracleComp spec α) → ↑oa.finSupport = oa.support
| _, _, pure' _ x => by simp
| _, _, query_bind' i t _ oa =>
  have : ∀ u, ↑(oa u).finSupport = (oa u).support := λ u ↦ coe_finSupport (oa u)
  by simp [this]

end OracleComp
