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

namespace OracleComp

def defaultResult {spec : OracleSpec} : {α : Type} → OracleComp spec α → α
| _, pure' α a => a
| _, query_bind' _ _ α oa => defaultResult (oa default)

instance (spec : OracleSpec) (α : Type) [h : Nonempty α] :
  Nonempty (OracleComp spec α) := h.elim (λ x ↦ ⟨pure' α x⟩)
instance (spec : OracleSpec) (α : Type) [Inhabited α] :
  Inhabited (OracleComp spec α) := ⟨pure' α default⟩
instance (spec : OracleSpec) (α : Type) [h : IsEmpty α] :
  IsEmpty (OracleComp spec α) := ⟨λ oa ↦ h.1 (defaultResult oa)⟩

variable {spec : OracleSpec} {α : Type}

def baseInhabited (oa : OracleComp spec α) : Inhabited α := ⟨oa.defaultResult⟩

section Monad

def bind' : (α β : Type) → OracleComp spec α → (α → OracleComp spec β) → OracleComp spec β
| _, _, pure' α a, ob => ob a
| _, β, query_bind' i t α oa, ob => query_bind' i t β (λ u ↦ bind' α β (oa u) ob)

instance (spec : OracleSpec) : Monad (OracleComp spec) :=
{ pure := @pure' spec, bind := @bind' spec }

@[simp] protected lemma pure'_eq_pure (spec : OracleSpec) (a : α) :
  pure' α a = (pure a : OracleComp spec α) := rfl

@[simp] protected lemma bind'_eq_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
  bind' α β oa ob = oa >>= ob := rfl

instance (spec : OracleSpec) : LawfulMonad (OracleComp spec) :=
LawfulMonad.mk' _
  (λ oa ↦ by
    induction' oa with α a i t α oa hoa; · rfl
    · exact congr_arg (query_bind' i t α) (funext (λ u ↦ hoa u)))
  (λ x ob ↦ rfl)
  (λ oa ob oc ↦ by
    induction' oa with α a i t α oa hoa; · rfl
    · exact congr_arg (query_bind' i t _) <| funext (λ u ↦ hoa u ob))

protected lemma bind_congr {oa oa' : OracleComp spec α} {ob ob' : α → OracleComp spec β}
  (h : oa = oa') (h' : ∀ x, ob x = ob' x) : oa >>= ob = oa' >>= ob' :=
h ▸ (congr_arg (λ ob ↦ oa >>= ob) (funext h'))

lemma ite_bind (p : Prop) [Decidable p] (oa oa' : OracleComp spec α)
  (ob : α → OracleComp spec β) : ite p oa oa' >>= ob = ite p (oa >>= ob) (oa' >>= ob) :=
by split_ifs <;> rfl

end Monad

section query

def query {spec : OracleSpec} (i : spec.ι) (t : spec.domain i) :
  OracleComp spec (spec.range i) :=
query_bind' i t (spec.range i) (pure' (spec.range i))

lemma query_def (i : spec.ι) (t : spec.domain i) :
  query i t = query_bind' i t (spec.range i) (pure' (spec.range i)) := rfl

@[simp] lemma query_bind'_eq_query_bind (i : spec.ι)
  (t : spec.domain i) (oa : spec.range i → OracleComp spec α) :
  query_bind' i t α oa = query i t >>= oa := rfl

@[reducible, inline] def coin : OracleComp coinSpec Bool :=
query (spec := coinSpec) () ()

@[reducible, inline] def uniformFin (n : ℕ) : OracleComp unifSpec (Fin (n + 1)) :=
query (spec := unifSpec) n ()

notation "$[0.." n "]" => uniformFin n

example : OracleComp unifSpec ℕ := do
  let x ←$[0..31415]
  let y ←$[0..16180]
  return x + 2 * y

end query

protected def induction_on {spec : OracleSpec}
  {C : Π {α : Type}, OracleComp spec α → Prop}
  (h_pure : ∀ {α : Type} (a : α), C (pure a))
  (h_query_bind : ∀ (i : spec.ι) (t : spec.domain i) {α : Type}
    (oa : spec.range i → OracleComp spec α),
    (∀ u, C (oa u)) → C (query i t >>= oa)) :
  {α : Type} → (oa : OracleComp spec α) → C oa
| _, (pure' α a) => h_pure a
| _, (query_bind' i t α oa) => h_query_bind i t oa
  (λ u ↦ OracleComp.induction_on h_pure h_query_bind (oa u))

section noConfusion

@[simp] lemma pure_inj (x x' : α) :
  (pure x : OracleComp spec α) = (pure x' : OracleComp spec α) ↔ x = x' :=
⟨λ h ↦ OracleComp.noConfusion h (λ _ hx ↦ eq_of_heq hx), λ h ↦ h ▸ rfl⟩

@[simp] lemma query_inj (i : spec.ι) (t t' : spec.domain i) :
  query i t = query i t' ↔ t = t' :=
⟨λ h ↦ OracleComp.noConfusion h (λ _ ht _ _ ↦ eq_of_heq ht), λ h ↦ h ▸ rfl⟩

@[simp] lemma query_bind_inj (i i' : spec.ι) (t : spec.domain i) (t' : spec.domain i')
  (oa : spec.range i → OracleComp spec α) (oa' : spec.range i' → OracleComp spec α) :
  query i t >>= oa = query i' t' >>= oa' ↔ ∃ h : i = i', h ▸ t = t' ∧ h ▸ oa = oa' := by
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · rw [← query_bind'_eq_query_bind, ← query_bind'_eq_query_bind] at h
    refine OracleComp.noConfusion h ?_
    rintro rfl ⟨rfl⟩ _ ⟨rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨rfl, rfl, rfl⟩ := h; rfl

@[simp] lemma pure_ne_query (i : spec.ι) (t : spec.domain i) (u : spec.range i) :
  pure u ≠ query i t := OracleComp.noConfusion

@[simp] lemma query_ne_pure (i : spec.ι) (t : spec.domain i) (u : spec.range i) :
  query i t ≠ pure u := OracleComp.noConfusion

@[simp] lemma pure_ne_query_bind (x : α) (i : spec.ι) (t : spec.domain i)
  (oa : spec.range i → OracleComp spec α) : pure x ≠ query i t >>= oa := OracleComp.noConfusion

@[simp] lemma query_bind_ne_pure (i : spec.ι) (t : spec.domain i)
  (oa : spec.range i → OracleComp spec α) : query i t >>= oa ≠ (pure x) := OracleComp.noConfusion

@[simp] lemma bind_eq_pure_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β) :
  oa >>= ob = pure y ↔ ∃ x : α, oa = pure x ∧ ob x = pure y := by
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · match oa with
    | pure' _ x => exact ⟨x, rfl, h⟩
    | query_bind' i t _ oa => simp at h
  · obtain ⟨x, hxa, hxb⟩ := h
    rw [hxa, pure_bind, hxb]

@[simp] lemma pure_eq_bind_iff (y : β) (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
  pure y = oa >>= ob ↔ ∃ x : α, oa = pure x ∧ ob x = pure y :=
eq_comm.trans (bind_eq_pure_iff oa ob y)

protected instance decidableEq {α : Type} [h : DecidableEq α] : DecidableEq (OracleComp spec α)
| pure' _ x, pure' _ x' => by simpa [pure_inj x x'] using h x x'
| pure' _ x, query_bind' i t _ oa => by simpa using Decidable.isFalse not_false
| query_bind' i t _ oa, pure' _ x => by simpa using Decidable.isFalse not_false
| query_bind' i t _ oa, query_bind' i' t' _ oa' => by
  by_cases hi : i = i'
  · induction hi; simp
    suffices Decidable (oa = oa') from inferInstance
    suffices Decidable (∀ u, oa u = oa' u) from decidable_of_iff' _ Function.funext_iff
    suffices ∀ u, Decidable (oa u = oa' u) from Fintype.decidableForallFintype
    exact λ u ↦ OracleComp.decidableEq (oa u) (oa' u)
  · simpa [hi] using Decidable.isFalse not_false

end noConfusion

end OracleComp
