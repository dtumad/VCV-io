/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Constructions.UniformSelect
import VCVio.OracleComp.DistSemantics.Seq
import VCVio.OracleComp.DistSemantics.List
import Init.Data.Vector.Lemmas

/-!
# Running a Computation Multiple Times

This file defines a function `replicate oa n` that runs the computation `oa` a total of `n` times,
returning the result as a list of length `n`.

Note that while the executions are independent, they may no longer be after calling `simulate`.
-/


open OracleSpec Vector

namespace OracleComp

@[simp]
lemma probFailure_mapM {ι : Type} {spec : OracleSpec ι} {α β : Type}
    (xs : List α) (f : α → OracleComp spec β) :
    [⊥ | xs.mapM f] = 1 - (xs.map (1 - [⊥ | f ·])).prod := by
  sorry

@[simp]
lemma probOutput_mapM {ι : Type} {spec : OracleSpec ι} {α β : Type}
    (xs : List α) (f : α → OracleComp spec β) (ys : List β) :
    [= ys | xs.mapM f] = if ys.length = xs.length then
      (List.zipWith (λ x y ↦ [= y | f x]) xs ys).prod else 0 := by
  sorry

/-- Run the computation `oa` repeatedly `n` times to get a vector of `n` results. -/
def replicate {ι : Type} {spec : OracleSpec ι} {α : Type}
    (n : ℕ) (oa : OracleComp spec α) : OracleComp spec (List α) :=
  (List.replicate n ()).mapM (λ () ↦ oa)

variable {ι : Type} {spec : OracleSpec ι} {α β : Type} (oa : OracleComp spec α)

@[simp]
lemma replicate_zero (oa : OracleComp spec α) :
    replicate 0 oa = return [] := rfl

@[simp]
lemma replicate_succ (oa : OracleComp spec α) (n : ℕ) :
    replicate (n + 1) oa = List.cons <$> oa <*> replicate n oa := by
  rw [replicate, List.replicate_succ, List.mapM_cons, seq_eq_bind, bind_map_left]; rfl

@[simp]
lemma replicate_pure (x : α) (n : ℕ) :
    (pure x : OracleComp spec α).replicate n = pure (List.replicate n x) := by
  induction n with
  | zero => rfl
  | succ n hn => simp [hn, List.replicate]

@[simp]
lemma probFailure_replicate (oa : OracleComp spec α) (n : ℕ) :
    [⊥ | oa.replicate n] = 1 - (1 - [⊥ | oa]) ^ n := by
  rw [replicate, probFailure_mapM, List.map_replicate, List.prod_replicate]

/-- The probability of getting a vector from `replicate` is the product of the chances of
getting each of the individual elements. -/
@[simp]
lemma probOutput_replicate (oa : OracleComp spec α) (n : ℕ) (xs : List α) :
    [= xs | oa.replicate n] = if xs.length = n then (xs.map ([= · | oa])).prod else 0 := by
  rw [replicate, probOutput_mapM, List.length_replicate]
  split_ifs with hxs
  · exact congr_arg List.prod <| List.ext_getElem (by simp [hxs]) (by simp)
  · rfl

@[simp]
lemma support_replicate (oa : OracleComp spec α) (n : ℕ) :
    (oa.replicate n).support = {xs | ∀ x ∈ xs, x ∈ oa.support} := by
  refine Set.ext (λ xs ↦ ?_)
  rw [← probOutput_pos_iff, probOutput_replicate]
  simp only [CanonicallyOrderedCommSemiring.list_prod_pos, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, probOutput_pos_iff, Set.mem_setOf_eq]
  sorry

-- @[simp] TODO: decidablility of this pred should be inferred from something else?
lemma support_replicate' (oa : OracleComp spec α) [DecidablePred (· ∈ oa.support)] (n : ℕ) :
    (oa.replicate n).support = {xs | xs.all (· ∈ oa.support)} := by
  refine Set.ext (λ xs ↦ ?_)
  rw [← probOutput_pos_iff, probOutput_replicate]
  simp only [CanonicallyOrderedCommSemiring.list_prod_pos, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, probOutput_pos_iff, List.all_eq_true, decide_eq_true_eq,
    Set.mem_setOf_eq]
  sorry

-- section SelectableTypeVector

-- /-- Vectors can be selected uniformly if the underlying type can be.
-- Note: this isn't very efficient as an actual implementation in practice. -/
-- instance (α : Type) [Fintype α] [Inhabited α] [SelectableType α] (n : ℕ) :
--     SelectableType (Vector α n) where
--   selectElem := _ <$> ($ᵗ α).replicate n
--   probOutput_selectElem_eq xs ys := by simp
--   probFailure_selectElem := by simp

-- end SelectableTypeVector

end OracleComp
