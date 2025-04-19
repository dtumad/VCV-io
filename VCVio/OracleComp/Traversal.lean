/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Support

/-!
# Traversing Possible Paths of a Computation.

This file defines functions `alwaysWhen` and `someWhen` that allow for traversing a computation's
structure to check some given predicates on each node, using a set of possible outputs for that
traversal. These definitions are `Prop` not `Bool` and should usually only be used in proofs,
not in defining an actual computaion.

The file also contains many special cases of these functions like `neverFailsWhen`.

-/

open OracleSpec

universe u v w

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type v}

section allWhen

variable (Q : {α : Type v} → OracleQuery spec α → Prop)
    (F : Prop) (oa : OracleComp spec α)
    (possible_outputs : {α : Type v} → OracleQuery spec α → Set α)

/-- All the given predicates hold on a computation when queries respond with
elements of `possible_outputs q` for every query `q` -/
def allWhen (possible_outputs : {α : Type v} → OracleQuery spec α → Set α)
    (oa : OracleComp spec α) : Prop := by
  induction oa using OracleComp.construct with
  | pure x => exact True
  | failure => exact F
  | query_bind q _ r => exact Q q ∧ ∀ x ∈ possible_outputs q, r x

@[simp] lemma allWhen_pure_iff (x : α) :
    (pure x : OracleComp spec α).allWhen Q F possible_outputs := True.intro

@[simp] lemma allWhen_failure_iff :
    (failure : OracleComp spec α).allWhen Q F possible_outputs ↔ F := Iff.rfl

@[simp] lemma allWhen_query_iff (q : OracleQuery spec α) :
    (q : OracleComp spec α).allWhen Q F possible_outputs ↔ Q q := by simp [allWhen]

@[simp] lemma allWhen_query_bind (q : OracleQuery spec α) (oa : α → OracleComp spec β) :
    ((q : OracleComp spec α) >>= oa).allWhen Q F possible_outputs ↔
      Q q ∧ ∀ x ∈ possible_outputs q, (oa x).allWhen Q F possible_outputs := by rfl

-- TODO: We need a full theory of `supportWhen` to make this work well.
@[simp] lemma allWhen_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (oa >>= ob).allWhen Q F possible_outputs ↔ oa.allWhen Q F possible_outputs ∧
      ∀ x ∈ oa.supportWhen possible_outputs, (ob x).allWhen Q F possible_outputs := by
  induction oa using OracleComp.inductionOn with
  | pure x => {
    simp [supportWhen]
  }
  | failure => {
    simp [supportWhen]
  }
  | query_bind i t oa h => {
    rw [bind_assoc, allWhen_query_bind]
    simp [h, supportWhen]

    sorry
  }

-- @[simp] lemma allWhen

end allWhen

variable (pure_pred : {α : Type v} → α → Prop)
    (query_pred : {α : Type v} → OracleQuery spec α → Prop)
    (fail_pred : Prop) (oa : OracleComp spec α)
    (possible_outputs : {α : Type v} → OracleQuery spec α → Set α)

/-- One of the given predicates hold on a computation when queries respond with
elements of `possible_outputs q` for every query `q` -/
def someWhen (possible_outputs : {α : Type v} → OracleQuery spec α → Set α)
    (oa : OracleComp spec α) : Prop := by
  induction oa using OracleComp.construct with
  | pure x => exact pure_pred x
  | failure => exact fail_pred
  | query_bind q _ r => exact query_pred q ∨ ∃ x ∈ possible_outputs q, r x

section neverFails

/-- `oa` never fails if when responses to queries `q` are in `possible_outputs q`. -/
def neverFailsWhen (oa : OracleComp spec α)
    (possible_outputs : {α : Type v} → OracleQuery spec α → Set α) : Prop :=
  oa.allWhen (fun _ => True) False possible_outputs

/-- `oa` never fails even when queries can output any possible value. -/
@[reducible, inline] def neverFails (oa : OracleComp spec α) : Prop :=
  oa.neverFailsWhen fun _ => Set.univ

-- TOOD: generalize when `hso` is `neverFailsWhen` for some other `poss`.
lemma neverFailsWhen_simulate {ι' : Type*} {spec' : OracleSpec ι'}
    (oa : OracleComp spec α)
    (possible_outputs : {α : Type v} → OracleQuery spec α → Set α)
    (h : neverFailsWhen oa possible_outputs)
    -- {m : Type v → Type _} [Monad m]
    (so : QueryImpl spec (OracleComp spec'))
    (h' : ∀ {α}, ∀ q : OracleQuery spec α, (so.impl q).support ⊆ possible_outputs q)
    (hso : ∀ {α}, ∀ q : OracleQuery spec α, neverFails (so.impl q)) :
    neverFails (simulateQ so oa) := sorry


-- lemma neverFails_eq_oracleComp_construct (oa : OracleComp spec α) :
--     oa.neverFails = OracleComp.construct
--       (fun _ ↦ True) (fun {β} _ _ r ↦ ∀ (x : β), r x) False oa := rfl

-- lemma neverFails_eq_freeMonad_construct (oa : OracleComp spec α) :
--     oa.neverFails = FreeMonad.construct
--       (fun t ↦ Option.rec False (fun _ ↦ True) t) (fun _ _ r ↦ ∀ x, r x) oa := rfl

@[simp]
lemma neverFails_pure (x : α) : neverFails (pure x : OracleComp spec α) := trivial

@[simp]
lemma neverFails_query (q : OracleQuery spec α) : neverFails (q : OracleComp spec α) := sorry
  -- fun _ => trivial

@[simp]
lemma neverFails_query_bind_iff {q : OracleQuery spec α} {oa : α → OracleComp spec β} :
    (liftM q >>= oa).neverFails ↔ ∀ x, neverFails (oa x) := sorry

alias ⟨neverFails_query_bind, _⟩ := neverFails_query_bind_iff

@[simp]
lemma not_neverFails_failure : ¬ neverFails (failure : OracleComp spec α) := fun h => h

@[simp]
lemma neverFails_guard (p : Prop) [Decidable p] (oa : OracleComp spec α) (h: oa.neverFails) :
    neverFails (if p then oa else failure) ↔ p := by
  split <;> simp [h] <;> trivial

@[simp]
lemma neverFails_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (oa >>= ob).neverFails ↔ oa.neverFails ∧ ∀ x ∈ oa.support, (ob x).neverFails := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | failure => simp
  | query_bind _ _ r ih => simp [ih, forall_and]; tauto

alias ⟨neverFails_bind, _⟩ := neverFails_bind_iff

-- @[simp]
-- lemma neverFails_map_iff (oa : OracleComp spec α) (f : α → β) :
--     neverFails (f <$> oa) ↔ neverFails oa := by
--   rw [map_eq_bind_pure_comp]
--   simp only [neverFails_bind_iff, Function.comp_apply, neverFails_pure, implies_true, and_true]

end neverFails

section mayFail

/-- `oa` might fail when responses to queries `q` are in `possible_outputs q`-/
def mayFailWhen (oa : OracleComp spec α)
    (possible_outputs : {α : Type v} → OracleQuery spec α → Set α) : Prop :=
  oa.someWhen (fun _ => False) (fun _ => False) True possible_outputs

-- lemma mayFailWhen_iff_not_neverFailWhen

/-- `oa` might fail if queries can output any possible value. -/
@[reducible, inline] def mayFail (oa : OracleComp spec α) : Prop :=
  mayFailWhen oa fun _ => Set.univ

end mayFail

end OracleComp
