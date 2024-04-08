/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.OracleAlg
import VCVio.OracleComp.Constructions.UniformSelect
import VCVio.OracleComp.SimSemantics.QueryTracking.CountingOracle

/-!
# Security Experiments

This file gives a basic way to represent security experiments, as an extension of `OracleAlg`.
The definition is meant to be simple enough to give useful lemmas while still being
able to represent most common use cases.

We also give a definition `SecAdv α β` of a security adversary with input `α` and output `β`,
as just a computation bundled with a bound on the number of queries it makes.

The main definition is `SecExp spec α β`, which extends `OracleAlg` with three functions:
* `inp_gen` that chooses an input for the experiment of type `α`
* `main` that takes an input and computes a result of type `β`
* `isValid` that decides whether the experiment succeeded
-/

open OracleComp OracleSpec ENNReal

/-- A security adversary bundling a computation with a bound on the number of queries it makes.
This is useful both for asymptotic security as well as in some concrete security bounds. -/
structure SecAdv (spec : OracleSpec)
    (α β : Type) where
  run : α → OracleComp spec β
  -- run_polyTime : polyTimeOracleComp run
  activeOracles : List spec.ι
  queryBound : QueryCount spec
  -- queryBound_is_bound : ∀ qc x y,
  --   (y, qc) ∈ (simulate countingOracle (run x) 0).support →
  --     ∀ i, qc i ≤ queryBound i
  -- mem_activeOracles_iff : ∀ i,
  --   i ∈ activeOracles ↔ queryBound i ≠ 0

  -- runQueryBound : QueryCount spec

namespace SecAdv

variable {spec : OracleSpec} {α β : Type}

end SecAdv

/-- A security experiment using oracles in `spec`, represented as an `OracleAlg`. -/
structure SecExp (spec : OracleSpec) (α : Type)
    extends OracleAlg spec where
  inpGen : OracleComp spec α
  main : α → OracleComp spec Bool

namespace SecExp

variable {spec : OracleSpec} {α β : Type}

def runExp (exp : SecExp spec α) :
    OracleComp unifSpec Bool :=
  exp.exec (exp.inpGen >>= exp.main)

@[simp]
lemma runExp_eq (exp : SecExp spec α) : exp.runExp = exp.exec
    (exp.inpGen >>= exp.main) := rfl

noncomputable def advantage (exp : SecExp spec α) : ℝ≥0∞ :=
  [= true | exp.exec (exp.inpGen >>= exp.main)]

@[simp]
lemma advantage_eq (exp : SecExp spec α) :
  exp.advantage = [= true | exp.runExp] := rfl

end SecExp
