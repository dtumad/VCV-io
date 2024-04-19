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

/-- Run the computation `oa` `n` times to get a `Vector α n` -/
def replicate (oa : OracleComp spec α) (n : ℕ) : OracleComp spec (Vector α n) :=
match n with
| 0 => return Vector.nil
| (n + 1) => (· ::ᵥ ·) <$> oa <*> replicate oa n

def replicate' (oa : OracleComp spec α) (n : ℕ) : OracleComp spec (List α) := do
    let mut xs : List α := []
    for _ in List.range n do
        let x ← oa
        xs ← pure (x :: xs)
    return xs

@[simp]
lemma replicate_zero (oa : OracleComp spec α) :
    oa.replicate 0 = pure nil := rfl

lemma replicate_zero' (oa : OracleComp spec α) :
    oa.replicate' 0 = pure [] := rfl

end OracleComp
