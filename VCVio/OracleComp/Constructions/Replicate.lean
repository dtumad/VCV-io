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

@[simp]
lemma replicate_zero (oa : OracleComp spec α) :
    oa.replicate 0 = pure nil := rfl

@[simp]
lemma replicate_succ (oa : OracleComp spec α) (n : ℕ) :
    oa.replicate (n + 1) = (· ::ᵥ ·) <$> oa <*> replicate oa n := rfl

end OracleComp
