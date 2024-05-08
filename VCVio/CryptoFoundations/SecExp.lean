/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.OracleAlg
import VCVio.OracleComp.Constructions.UniformSelect

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
  queryBound : spec.ι → ℕ
  -- queryBound_isQueryBound (x : α) : IsQueryBound (run x) queryBound
  activeOracles : List spec.ι -- Canonical ordering of oracles
  -- mem_activeOracles_iff : ∀ i, i ∈ activeOracles ↔ queryBound i ≠ 0

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

noncomputable def advantage (exp : SecExp spec α) : ℝ≥0∞ :=
    [= true | exp.exec (exp.inpGen >>= exp.main)]

lemma advantage_eq (exp : SecExp spec α) :
    exp.advantage = [= true | exp.exec (exp.inpGen >>= exp.main)] := rfl

@[simp]
lemma advantage_eq_one_iff (exp : SecExp spec α) : exp.advantage = 1 ↔
    false ∉ (exp.exec (exp.inpGen >>= exp.main)).support := by
  simp only [advantage_eq, probOutput_eq_one_iff, OracleAlg.exec_bind, support_bind,
    Set.subset_singleton_iff, Set.mem_iUnion, exists_prop, Prod.exists, forall_exists_index,
    and_imp, Bool.forall_bool, imp_false, implies_true, and_true, not_exists, not_and]

@[simp]
lemma advantage_eq_zero_iff (exp : SecExp spec α) : exp.advantage = 0 ↔
    true ∉ (exp.exec (exp.inpGen >>= exp.main)).support := by
  rw [advantage_eq, probOutput_eq_zero_iff]

@[simp]
lemma advantage_pos_iff (exp : SecExp spec α) : 0 < exp.advantage ↔
    true ∈ (exp.exec (exp.inpGen >>= exp.main)).support := by
  rw [pos_iff_ne_zero, ne_eq, advantage_eq_zero_iff, not_not]

end SecExp
