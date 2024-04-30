/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.EvalDist

/-!
# Running a Computation Multiple Times

This file defines a function `replicate oa n` that runs the computation `oa` a total of `n` times,
returning the result as a vector of length `n`.

Note that while the executions are independent, they may no longer be after calling `simulate`.
-/

open OracleSpec Vector

namespace OracleComp

variable {spec : OracleSpec} {α β : Type}

/-- Run the computation `oa` `n` times to get a `Vector α n` -/
def replicate (oa : OracleComp spec α) (n : ℕ) : OracleComp spec (Vector α n) :=
    match n with
    | 0 => return Vector.nil
    | (n + 1) => (· ::ᵥ ·) <$> oa <*> replicate oa n

@[simp low]
lemma replicate_zero (oa : OracleComp spec α) : oa.replicate 0 = pure Vector.nil := rfl

@[simp low]
lemma replicate_succ (oa : OracleComp spec α) (n : ℕ) :
    oa.replicate (n + 1) = (· ::ᵥ ·) <$> oa <*> replicate oa n := rfl

-- @[simp]
-- lemma replicate_add (oa : OracleComp spec α) (n m : ℕ) :
--         (replicate oa (n + m)) = (· ++ ·) <$> replicate oa n <*> replicate oa m := by
--     induction n with
--     | zero => simp only [Nat.zero_eq, zero_add, replicate_zero,
--         map_pure, List.nil_append, pure_id'_seq]
--     | succ n hn => simp only [Nat.succ_add, replicate_succ, map_eq_bind_pure_comp,
--         Function.comp, hn, seq_eq_bind, bind_assoc, pure_bind, List.cons_append]

@[simp]
lemma probOutput_replicate (oa : OracleComp spec α) (n : ℕ) (xs : Vector α n) :
        [= xs | replicate oa n] =  (xs.toList.map ([= · | oa])).prod := by
        --if xs.length = n then (xs.map ([= · | oa])).prod else 0 := by
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
        (replicate oa n).support = {xs | ∀ x ∈ xs.toList, x ∈ oa.support} := by
    sorry

end OracleComp
