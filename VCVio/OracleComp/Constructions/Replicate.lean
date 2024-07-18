/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Constructions.UniformSelect
import VCVio.OracleComp.DistSemantics.Seq

/-!
# Running a Computation Multiple Times

This file defines a function `replicate oa n` that runs the computation `oa` a total of `n` times,
returning the result as a list of length `n`.

Note that while the executions are independent, they may no longer be after calling `simulate`.
-/

open OracleSpec Mathlib

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-- Run the computation `oa` repeatedly `n` times to get a list of `n` results. -/
-- def replicate (oa : OracleComp spec α) : ℕ → OracleComp spec (List α)
--   | 0 => return []
--   | n + 1 => (· :: ·) <$> oa <*> replicate oa n

-- TODO: Decide if a version like this is better?
def replicate (oa : OracleComp spec α) : (n : ℕ) → OracleComp spec (Vector α n)
  | 0 => pure Vector.nil
  | n + 1 => (· ::ᵥ ·) <$> oa <*> replicate oa n

variable (oa : OracleComp spec α) (n m : ℕ)

@[simp]
lemma replicate_zero : oa.replicate 0 = pure Vector.nil := rfl

@[simp]
lemma replicate_succ : oa.replicate (n + 1) = (· ::ᵥ ·) <$> oa <*> replicate oa n := rfl

lemma replicate_add_zero : oa.replicate (n + 0) = oa.replicate n := by simp

section zero_add

/-- Running a computation `0 + n` times is the same as running it `n` times.
Because `0 + n` and `n` are not definitionally equal, regular equality will not typecheck. -/
lemma replicate_zero_add_heq : HEq (oa.replicate (0 + n)) (oa.replicate n) := by
  cases h : 0 + n <;> {rw [zero_add] at h; cases h; rfl}

/-- Running a computation `0 + n` times is the same as running it `n` times.
Requires substituting the equality between the two to properly typecheck the vector types. -/
lemma replicate_zero_add : oa.replicate (0 + n) = (zero_add n).symm ▸ oa.replicate n := by
  refine eq_of_heq <| (replicate_zero_add_heq oa n).trans <| (heq_eqRec_iff_heq _ _ _).2 HEq.rfl

end zero_add

section comm

/-- Running a computation `n + m` times is the same as running it `n` times then `m` times.
Because `n + m` and `m + n` are not definitionally equal, regular equality will not typecheck. -/
lemma replicate_add_comm_heq : HEq (oa.replicate (n + m)) (oa.replicate (m + n)) := by
  cases h : n + m
  · cases h' : m + n
    · exact HEq.rfl
    · rw [add_comm n m, h'] at h
      exact (Nat.succ_ne_zero _ h).elim
  · cases h' : m + n
    · rw [add_comm m n, h] at h'
      exact (Nat.succ_ne_zero _ h').elim
    · rw [add_comm n m, h', Nat.add_one_inj] at h
      cases h
      rfl

lemma replicate_add_comm : oa.replicate (n + m) = add_comm n m ▸ oa.replicate (m + n) := by
  refine eq_of_heq <| (replicate_add_comm_heq oa n m).trans <| (heq_eqRec_iff_heq _ _ _).2 HEq.rfl

end comm

/-- Running a computation `0 + n` times is the same as running it `n` times.
Requires substituting the equality between the two to properly typecheck the vector types. -/
lemma replicate_add (oa : OracleComp spec α) (n m : ℕ) :
    (replicate oa (n + m)) = Vector.append <$> replicate oa n <*> replicate oa m := by
  induction n with
  | zero => {
    refine eq_of_heq ((replicate_zero_add_heq oa m).trans ?_)

    simp [seq_eq_bind, map_eq_bind_pure_comp, Function.comp]
    sorry
  }
  | succ n hn => {
    sorry
  }

lemma List.Injective2_cons {α : Type} : Function.Injective2 (List.cons (α := α)) := by
  sorry

@[simp]
lemma probOutput_replicate (oa : OracleComp spec α) (n : ℕ) (xs : Vector α n) :
    [= xs | replicate oa n] = (xs.toList.map ([= · | oa])).prod := by
  sorry
  -- match xs with
  -- | [] => sorry
  -- | x :: xs => {
  --   induction n with
  --   | zero => sorry
  --   | succ n hn => {
  --     sorry
  --   }
  -- }
  -- induction n with
  -- | zero => cases xs <;> simp
  -- | succ n hn => {
  --   match xs with
  --   | [] => simp
  --   | x :: xs => {
  --     rw [replicate_succ]
  --     rw [probOutput_seq_map_eq_mul_of_injective2 _ _ _ (List.Injective2_cons)]



  --   }
  -- }

#check Vector

@[simp]
lemma support_replicate (oa : OracleComp spec α) (n : ℕ) :
    (replicate oa n).support = {xs | ∀ x ∈ xs.toList, x ∈ oa.support} := by
  sorry

/-- Vectors can be selected uniformly if the underlying type can be.
Note: this isn't very efficient as an actual implementation in practice. -/
instance (α : Type) [Fintype α] [Inhabited α] [SelectableType α] (n : ℕ) :
    SelectableType (Vector α n) where
  selectElem := (λ xs ↦ Vector.ofFn (λ i ↦ xs[i]!)) <$> replicate ($ᵗ α) n
  probOutput_selectElem := sorry

end OracleComp
