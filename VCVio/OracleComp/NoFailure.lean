/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.Support

/-!
# Computations that Never Fail

This file defines a class `OracleComp.NoFailure` for computations that never fail regardless
of the behavior of oracles. This can be useful for simplifying some probability calculations.
-/

universe u v w

open OracleSpec

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type u}

class noFailure {α : Type u} (oa : OracleComp spec α) : Prop where
  no_failure : by induction oa using OracleComp.construct with
    | pure _ => exact True
    | failure => exact False
    | query_bind _ _ r => exact ∀ x, r x

instance noFailure_pure (x : α) : noFailure (pure x : OracleComp spec α) where
  no_failure := trivial

instance noFailure_query (q : OracleQuery spec α) : noFailure (q : OracleComp spec α) where
  no_failure := fun _ => trivial

@[simp]
lemma not_noFailure_failure : ¬ noFailure (failure : OracleComp spec α) := fun ⟨h⟩ => h

@[simp]
lemma noFailure_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (oa >>= ob).noFailure ↔ oa.noFailure ∧ ∀ x ∈ oa.support, (ob x).noFailure := by
  sorry

instance {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    [h : noFailure oa] [h' : ∀ x, noFailure (ob x)] : noFailure (oa >>= ob) where
  no_failure := by
    induction oa using OracleComp.inductionOn generalizing h with
    | pure x => exact (h' x).no_failure
    | failure => exact h.no_failure.elim
    | query_bind _ _ r => sorry

@[simp]
lemma noFailure_map_iff (oa : OracleComp spec α) (f : α → β) :
    noFailure (f <$> oa) ↔ noFailure oa := by sorry

instance {oa : OracleComp spec α} {f : α → β} [noFailure oa] : noFailure (f <$> oa) := by
  sorry

@[simp]

instance {α : Type u} [spec.FiniteRange] : DecidablePred (@OracleComp.noFailure _ spec α) :=
  fun oa => by induction oa using OracleComp.construct with
  | pure x =>
      refine Decidable.isTrue (noFailure_pure x)
  | failure =>
      refine Decidable.isFalse not_noFailure_failure
  | query_bind q _ r =>
      cases q
      simp only [noFailure_bind_iff, noFailure_query, support_liftM, Set.mem_univ, forall_const, true_and]
      exact Fintype.decidableForallFintype


end OracleComp
