/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import «VCV-io».OracleComp.OracleSpec

open OracleSpec

inductive OracleComp (spec : OracleSpec) : Type → Type 1
  | pure' (α : Type) (a : α) : OracleComp spec α
  | query_bind' (i : spec.ι) (t : spec.domain i) (α : Type)
      (oa : spec.range i → OracleComp spec α) : OracleComp spec α

namespace OracleComp

variable {spec : OracleSpec} {α β γ : Type}

def default_result : {α : Type} → OracleComp spec α → α
  | _, pure' α a => a
  | _, query_bind' _ _ α oa => default_result (oa default)

instance (spec : OracleSpec) (α : Type) [h : Nonempty α] :
  Nonempty (OracleComp spec α) := h.elim (λ x ↦ ⟨pure' α x⟩)

instance (spec : OracleSpec) (α : Type) [Inhabited α] :
  Inhabited (OracleComp spec α) := ⟨pure' α default⟩

instance (spec : OracleSpec) (α : Type) [h : IsEmpty α] :
  IsEmpty (OracleComp spec α) := ⟨λ oa ↦ h.1 (default_result oa)⟩

def base_inhabited (oa : OracleComp spec α) : Inhabited α := ⟨oa.default_result⟩

section Monad

/-- We define a monadic bind operation on `oracle_comp` by induction on the first computation.
With this definition `oracle_comp` satisfies the monad laws (see `oracle_comp.is_lawful_monad`). -/
def bind' : (α β : Type) → OracleComp spec α → (α → OracleComp spec β) → OracleComp spec β
| _, _, pure' α a, ob => ob a
| _, β, query_bind' i t α oa, ob => query_bind' i t β (λ u ↦ bind' α β (oa u) ob)

instance (spec : OracleSpec) : Monad (OracleComp spec) :=
{ pure := @pure' spec, bind := @bind' spec }

protected lemma pure_def (spec : OracleSpec) {α : Type} (a : α) :
  (pure a : OracleComp spec α) = pure' α a := rfl

protected lemma bind_def {spec : OracleSpec} {α β : Type}
  (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
  oa >>= ob = bind' α β oa ob := rfl

instance (spec : OracleSpec) : LawfulMonad (OracleComp spec) :=
LawfulMonad.mk' _
  (λ oa ↦ by
    induction' oa with α a i t α oa hoa
    · rfl
    · exact congr_arg (query_bind' i t α) (funext (λ u ↦ hoa u)))
  (λ x ob ↦ rfl)
  (λ oa ob oc ↦ by
    induction' oa with α a i t α oa hoa
    · rfl
    · refine congr_arg (query_bind' i t _) <| funext (λ u ↦ hoa u ob))

-- @[simp] protected lemma pure'_eq_return (spec) :
--   (pure' α : α → oracle_comp spec α) = return := funext (λ a ↦ rfl)

-- @[simp] protected lemma pure_eq_return (spec) :
--   (pure : α → oracle_comp spec α) = return := funext (λ a, rfl)

-- @[simp] protected lemma bind'_eq_bind (spec) :
--   (bind' α β : oracle_comp spec α → (α → oracle_comp spec β) → oracle_comp spec β) = (>>=) := rfl

-- protected lemma bind_return_comp_eq_map (oa : OracleComp spec α) (f : α → β) :
--   oa >>= pure ∘ f = f <$> oa := rfl

-- protected lemma map_eq_bind_return_comp (oa : oracle_comp spec α) (f : α → β) :
--   f <$> oa = oa >>= return ∘ f := rfl

-- protected lemma return_bind (a : α) (ob : α → oracle_comp spec β) :
--   return a >>= ob = ob a := pure_bind a ob

-- protected lemma bind_return (oa : oracle_comp spec α) : oa >>= return = oa := bind_pure oa

-- @[simp] lemma bind_query_bind' (i : spec.ι) (t : spec.domain i)
--   (oa : spec.range i → oracle_comp spec α) (ob : α → oracle_comp spec β) :
--   (query_bind' i t α oa) >>= ob = query_bind' i t β (λ u, oa u >>= ob) := rfl

-- @[simp] lemma map_map_eq_map_comp (oa : oracle_comp spec α) (f : α → β) (g : β → γ) :
--   g <$> (f <$> oa) = (g ∘ f) <$> oa :=
-- by simp [oracle_comp.map_eq_bind_return_comp, bind_assoc]

-- lemma map_return (f : α → β) (a : α) : f <$> (return a : OracleComp spec α) = return (f a) := rfl

protected lemma bind_congr {oa oa' : OracleComp spec α} {ob ob' : α → OracleComp spec β}
  (h : oa = oa') (h' : ∀ x, ob x = ob' x) : oa >>= ob = oa' >>= ob' :=
h ▸ (congr_arg (λ ob ↦ oa >>= ob) (funext h'))

lemma ite_bind (p : Prop) [Decidable p] (oa oa' : OracleComp spec α)
  (ob : α → OracleComp spec β) : ite p oa oa' >>= ob = ite p (oa >>= ob) (oa' >>= ob) :=
by split_ifs <;> rfl

-- lemma bind_seq (oa : OracleComp spec α) (og : OracleComp spec (α → β))
--   (oc : β → OracleComp spec γ) : (og <*> oa) >>= oc = og >>= λ f ↦ oa >>= (oc ∘ f) :=
-- by simp [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc]

end Monad

section query

/-- Shorthand for running a query and returning the value.
Generally this should be preferred over using `query_bind'` directly. -/
def query (i : spec.ι) (t : spec.domain i) : OracleComp spec (spec.range i) :=
query_bind' i t (spec.range i) (pure' (spec.range i))

lemma query_def (i : spec.ι) (t : spec.domain i) :
  query i t = query_bind' i t (spec.range i) (pure' (spec.range i)) := rfl

@[simp] lemma query_bind'_eq_query_bind (i : spec.ι)
  (t : spec.domain i) (oa : spec.range i → OracleComp spec α) :
  query_bind' i t α oa = query i t >>= oa := rfl

@[reducible, inline] def coin : OracleComp coinSpec Bool :=
query (spec := coinSpec) () ()

end query

end OracleComp
