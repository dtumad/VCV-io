/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import «VCV-io».OracleComp.OracleComp
import Mathlib.Data.Set.Finite

namespace OracleComp

variable {spec : OracleSpec} {α β : Type}

/-- The `support` of a computation `oa` is the set of all possible output values,
assuming that all output values of the oracles are possible.
This is naturally compatible with `evalDist` where the oracles respond uniformly. -/
def support : OracleComp spec α → Set α
| pure' _ x => {x}
| query_bind' _ _ _ oa => ⋃ u, (oa u).support

/-- Given a `DecidableEq` instance on the return type, we can construct
a `Finset` of possible outputs. Without this we can't remove duplicate values from
the list of outputs being constructed. This also relies on the `DecidableEq` instances
on `spec.range i` that are included in the definition of `OracleSpec`. -/
def finSupport [DecidableEq α] : OracleComp spec α → Finset α
| pure' _ x => {x}
| query_bind' _ _ _ oa => Finset.biUnion Finset.univ (λ u ↦ (oa u).finSupport)

section basic

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
| h_query_bind i t oa hoa =>
    simpa [bind_assoc, ← query_bind'_eq_query_bind, support, hoa]
      using Set.iUnion_comm _

@[simp] lemma finSupport_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
  [DecidableEq α] → [DecidableEq β] →
    (oa >>= ob).finSupport = oa.finSupport.biUnion (λ x ↦ (ob x).finSupport) :=
by induction oa using OracleComp.induction_on with
| h_pure _ => simp
| h_query_bind i t oa hoa =>
    intros hα hβ; apply Finset.coe_inj.1
    simpa [bind_assoc, ← query_bind'_eq_query_bind, finSupport, hoa] using Set.iUnion_comm _

/-- The support of a computation is finite when viewed as a type. -/
instance support_finite (oa : OracleComp spec α) : Finite ↥oa.support :=
by induction oa using OracleComp.induction_on with
| h_pure x => exact Set.finite_singleton x
| h_query_bind _ _ oa hoa => exact Set.finite_iUnion hoa

/-- With a `DecidableEq` instance we can show that the support is actually a `Fintype`,
rather than just `Finite` as in `support_finite`. -/
instance support_fintype : {α : Type} → [DecidableEq α] →
  (oa : OracleComp spec α) → Fintype ↥oa.support
| _, _, pure' _ x => Fintype.subtypeEq x
| _, _, query_bind' _ _ _ oa =>
    have : ∀ u, Fintype (oa u).support := λ u ↦ support_fintype (oa u)
    Set.fintypeiUnion _

lemma support_nonempty (oa : OracleComp spec α) : oa.support.Nonempty :=
by induction oa using OracleComp.induction_on with
| h_pure x => exact Set.singleton_nonempty x
| h_query_bind _ _ oa hoa => exact Set.nonempty_iUnion.2 ⟨default, hoa default⟩

end basic

section coe

/-- `finSupport` when viewed as a `Set` gives the regular `support` of the computation.  -/
@[simp] lemma coe_finSupport : {α : Type} → [DecidableEq α] →
  (oa : OracleComp spec α) → ↑oa.finSupport = oa.support
| _, _, pure' _ x => by simp
| _, _, query_bind' i t _ oa =>
  have : ∀ u, ↑(oa u).finSupport = (oa u).support := λ u ↦ coe_finSupport (oa u)
  by simp [this]

lemma finSupport_eq_iff_support_eq_coe [DecidableEq α] (oa : OracleComp spec α)
  (s : Finset α) : oa.finSupport = s ↔ oa.support = ↑s :=
Finset.coe_inj.symm.trans (by rw [coe_finSupport])

lemma eq_finSupport_iff_coe_eq_support [DecidableEq α] (oa : OracleComp spec α)
  (s : Finset α) : s = oa.finSupport ↔ ↑s = oa.support :=
Finset.coe_inj.symm.trans (by rw [coe_finSupport])

end coe

@[simp] lemma support_map (oa : OracleComp spec α) (f : α → β) :
  (f <$> oa).support = f '' oa.support :=
by simp [map_eq_pure_bind, ← Set.image_eq_iUnion]
@[simp] lemma fin_support_map [DecidableEq α] [DecidableEq β]
  (oa : OracleComp spec α) (f : α → β) : (f <$> oa).finSupport = oa.finSupport.image f :=
by simp [finSupport_eq_iff_support_eq_coe]

@[simp] lemma support_seq (oa : OracleComp spec α) (og : OracleComp spec (α → β)) :
  (og <*> oa).support = ⋃ g ∈ og.support, g '' oa.support :=
by simp [seq_eq_bind_map]
@[simp] lemma finSupport_seq [DecidableEq α] [DecidableEq β] [DecidableEq (α → β)]
  (oa : OracleComp spec α) (og : OracleComp spec (α → β)) :
  (og <*> oa).finSupport = og.finSupport.biUnion (λ g ↦ oa.finSupport.image g) :=
by simp [seq_eq_bind_map]

@[simp] lemma support_ite (p : Prop) [Decidable p] (oa oa' : OracleComp spec α) :
  (ite p oa oa').support = ite p oa.support oa'.support :=
apply_ite support p oa oa'
@[simp] lemma finSupport_ite [DecidableEq α] (p : Prop) [Decidable p]
  (oa oa' : OracleComp spec α) : (ite p oa oa').finSupport =
    ite p oa.finSupport oa'.finSupport :=
apply_ite finSupport p oa oa'

@[simp] lemma support_coin : coin.support = {true, false} :=
by simp [Set.ext_iff, coin, support_query (spec := coinSpec)]
@[simp] lemma finSupport_coin : coin.finSupport = {true, false} :=
by simp [finSupport_eq_iff_support_eq_coe]

@[simp] lemma support_uniformFin (n : unifSpec.ι) : ($[0..n]).support = Set.univ :=
support_query n ()
@[simp] lemma finSupport_uniformFin (n : unifSpec.ι) : ($[0..n]).finSupport = Finset.univ :=
finSupport_query n ()

example : support (do
  let b ← coin; let b' ← coin
  let x ← (if b && b' then return 0 else return 1);
  let z ← (if b && b' then return x else return 0);
  return (x * z)) = {0} :=
by simp

example : finSupport (do
  let b ← coin; let b' ← coin
  let x ← (if b || b' then return 0 else return 1);
  let z ← (if b || b' then return x else return 0);
  return (x * z)) = {0} :=
by simp

end OracleComp
