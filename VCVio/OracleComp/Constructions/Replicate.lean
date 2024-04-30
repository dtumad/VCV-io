/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Constructions.UniformSelect

/-!
# Running a Computation Multiple Times

This file defines a function `replicate oa n` that runs the computation `oa` a total of `n` times,
returning the result as a list of length `n`.

Note that while the executions are independent, they may no longer be after calling `simulate`.
-/

open OracleSpec Vector

namespace OracleComp

variable {spec : OracleSpec} {α β : Type}

/-- Run the computation `oa` repeatedly `n` times to get a list of `n` results. -/
def replicate (oa : OracleComp spec α) (n : ℕ) : OracleComp spec (List α) :=
    match n with
    | 0 => return []
    | (n + 1) => (· :: ·) <$> oa <*> replicate oa n

def replicateVec (oa : OracleComp spec α) (n : ℕ) : OracleComp spec (Vector α n) :=
    (λ xs ↦ Vector.ofFn (λ i ↦ if h : ↑i < xs.length then xs[i]'h else oa.defaultResult))
        <$> replicate oa n

@[simp low]
lemma replicate_zero (oa : OracleComp spec α) : oa.replicate 0 = return [] := rfl

@[simp low]
lemma replicate_succ (oa : OracleComp spec α) (n : ℕ) :
    oa.replicate (n + 1) = (· :: ·) <$> oa <*> replicate oa n := rfl

@[simp]
lemma replicate_add (oa : OracleComp spec α) (n m : ℕ) :
        (replicate oa (n + m)) = (· ++ ·) <$> replicate oa n <*> replicate oa m := by
    induction n with
    | zero => simp only [Nat.zero_eq, zero_add, replicate_zero,
        map_pure, List.nil_append, pure_id'_seq]
    | succ n hn => simp only [Nat.succ_add, replicate_succ, map_eq_bind_pure_comp,
        Function.comp, hn, seq_eq_bind, bind_assoc, pure_bind, List.cons_append]

@[simp]
lemma probOutput_replicate (oa : OracleComp spec α) (n : ℕ) (xs : List α) :
        [= xs | replicate oa n] = if xs.length = n then (xs.map ([= · | oa])).prod else 0 := by
    induction n with
    | zero => {
        sorry
        -- cases xs
        -- · simp
        -- · simp
    }
    | succ n => {
        simp
        sorry
    }

@[simp]
lemma support_replicate (oa : OracleComp spec α) (n : ℕ) :
        (replicate oa n).support = {xs | ∀ x ∈ xs, x ∈ oa.support} := by
    sorry

/-- Vectors can be selected uniformly if the underlying type can be.
Note: this isn't very efficient as an actual implementation in practice. -/
instance (α : Type) [Fintype α] [Inhabited α] [SelectableType α] (n : ℕ) :
    SelectableType (Vector α n) where
  selectElem := (λ xs ↦ Vector.ofFn (λ i ↦ if h : ↑i < xs.length then xs[i]'h else default))
        <$> replicate ($ᵗ α) n
  probOutput_selectElem := sorry

end OracleComp
