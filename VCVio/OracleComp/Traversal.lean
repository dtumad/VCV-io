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

variable
    (query_pred : {α : Type v} → OracleQuery spec α → Prop)
    (fail_pred : Prop) (oa : OracleComp spec α)
    (possible_outputs : {α : Type v} → OracleQuery spec α → Set α)

/-- All the given predicates hold on a computation when queries respond with
elements of `possible_outputs q` for every query `q` -/
def allWhen (possible_outputs : {α : Type v} → OracleQuery spec α → Set α)
    (oa : OracleComp spec α) : Prop := by
  induction oa using OracleComp.construct with
  | pure x => exact True
  | failure => exact fail_pred
  | query_bind q _ r => exact query_pred q ∧ ∀ x ∈ possible_outputs q, r x

@[simp] lemma allWhen_pure (x : α) : (pure x : OracleComp spec α).allWhen
     query_pred fail_pred possible_outputs := True.intro

@[simp] lemma allWhen_failure_iff : (failure : OracleComp spec α).allWhen
   query_pred fail_pred possible_outputs ↔ fail_pred := Iff.rfl

@[simp] lemma allWhen_query_iff (q : OracleQuery spec α) : (q : OracleComp spec α).allWhen
    query_pred fail_pred possible_outputs ↔ query_pred q := by simp [allWhen]

@[simp] lemma allWhen_query_bind (q : OracleQuery spec α) (oa : α → OracleComp spec β) :
    ((q : OracleComp spec α) >>= oa).allWhen query_pred fail_pred possible_outputs ↔ query_pred q ∧
      ∀ x ∈ possible_outputs q, (oa x).allWhen query_pred fail_pred possible_outputs := by rfl

-- TODO: We need a full theory of `supportWhen` to make this work well.
-- @[simp] lemma allWhen_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
--     (oa >>= ob).allWhen query_pred fail_pred possible_outputs ↔
--       oa.allWhen query_pred fail_pred possible_outputs ∧
--         ∀ x ∈ oa.supportWhen possible_outputs, (ob x).allWhen query_pred fail_pred possible_outputs := by
--   induction oa using OracleComp.inductionOn with
--   | pure x => {
--     simp [supportWhen]
--   }
--   | failure => {
--     simp [supportWhen]
--   }
--   | query_bind i t oa h => {
--     rw [bind_assoc, allWhen_query_bind]
--     simp [h, supportWhen]
--     rw [and_assoc]
--     refine and_congr_right fun _ => ?_
--   }

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

section neverFail

/-- `oa` never fails if when responses to queries `q` are in `possible_outputs q`. -/
def neverFailWhen (oa : OracleComp spec α)
    (possible_outputs : {α : Type v} → OracleQuery spec α → Set α) : Prop :=
  oa.allWhen (fun _ => True) False possible_outputs

/-- `oa` never fails even when queries can output any possible value. -/
@[reducible, inline] def neverFail (oa : OracleComp spec α) : Prop :=
  oa.neverFailWhen fun _ => Set.univ

end neverFail

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
