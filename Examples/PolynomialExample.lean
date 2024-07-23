/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio

open Sum Polynomial OracleSpec OracleComp

variable {α β γ : Type} {R : Type} [Semiring R]
  [Fintype R] [DecidableEq R] [Inhabited R]
  [SelectableType R]

-- Second oracle take in values in `R` and "evaluate" the polynomial on them
-- At this point oracle is a black box, no actual behavior specified
-- But for the purpose of defining the computation that isn't needed
example : OracleComp (unifSpec ++ₒ (R →ₒ R)) R := do
  let x₁ : R ←$ᵗ R
  let x₂ : R ←$ᵗ R
  -- Query the `inr` oracle to evaluate polynomial on some values
  let query_result₁ : R ← query (inr ()) (x₁ + x₂)
  let query_result₂ : R ← query (inr ()) (x₁ + 2 * x₂)
  return query_result₁ + query_result₂

-- `SimOracle` for actually implementing oracle behavior
-- Simulates the oracle `R →ₒ R` by evaluating the polynomial on queries
-- This reduces the oracles to just `unifSpec` (although really anything could go there)
-- Assumes the polynomial is globally fixed so just take `p` as input
-- No internal state so we use `Unit` type for that
def polyEvalOracle (p : R[X]) : (R →ₒ R) →[Unit]ₛₒ unifSpec :=
  λ () t () ↦ do
    let eval_result := p.eval t
    return (eval_result, ())

-- Run a computation `oa : OracleComp (unifSpec ++ₒ (R →ₒ R)) α` using the above
-- `polyGenerator` is the computation that produces the polynomial to use for oracle
noncomputable example (polyGenerator : OracleComp unifSpec (R[X]))
    (oa : OracleComp (unifSpec ++ₒ (R →ₒ R)) α) :
    OracleComp unifSpec α := do
  let p ← polyGenerator
  -- Leave the first oracle alone and use `p` to answer the second oracle
  let x ← simulate' (idOracle ++ₛₒ polyEvalOracle p) ((), ()) oa
  let q : R[X] := X ^ 2 + X + 1
  -- Same thing with a fixed polynomial
  let y ← simulate' (idOracle ++ₛₒ polyEvalOracle q) ((), ()) oa
  let b ←$ᵗ Bool
  return if b then x else y

-- Version that stores the polynomial in state of the oracle
-- Only needed if the polynomial being used will change during the execution
def polyEvalOracle_state : (R →ₒ R) →[R[X]]ₛₒ unifSpec :=
  λ () t p ↦ do
    let eval_result := p.eval t
    return (eval_result, p) -- Could modify the internal polynomial `p` first
