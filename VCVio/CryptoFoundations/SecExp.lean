/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.ExecutionMethod
import VCVio.OracleComp.Constructions.UniformSelect
import VCVio.OracleComp.QueryBound

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

universe u v w

open OracleComp OracleSpec ENNReal Polynomial Prod

/-- A security adversary bundling a computation with a bound on the number of queries it makes,
where the bound must be shown to satisfy `IsQueryBound`.
We also require an explicit list of all oracles used in the computation,
which is necessary in order to make certain reductions computable. -/
structure SecAdv {ι : Type u} [DecidableEq ι]
    (spec : OracleSpec ι) (α β : Type u) where
  run : α → OracleComp spec β
  qb : ι → ℕ
  qb_isQueryBound (x : α) : IsQueryBound (run x) (qb)
  activeOracles : List ι
  mem_activeOracles_iff (i : ι) : i ∈ activeOracles ↔ qb i ≠ 0

namespace SecAdv

variable {ι : Type u} {spec : OracleSpec ι} {α β : Type u}

end SecAdv

-- /-- Structure to represent a security experiment. `spec` is the set of oracles available
-- in the experiment, and the structure extends an oracle implementation for `spec`.
-- `σ` is the state type for the implementation.
-- The expirement is considered successfull unless it terminates with `failure`.
-- This is usually based off of `guard` statements but can be anything.

-- TODO: evaluate whether this simplifies things for users in practice. -/
-- structure SecExp (m : Type v → Type w)
--     extends ExecutionMethod m where
--   main : m Unit

-- namespace SecExp

-- variable {ι : Type u} {spec : OracleSpec ι} {em : Type → Type w}
--     [AlternativeMonad em] [LawfulAlternative em]

-- section advantage

-- noncomputable def advantage (exp : SecExp spec em) : ℝ≥0∞ :=
--   1 - [⊥ | exp.exec_as_probComp exp.main]

-- @[simp]
-- lemma advantage_eq_zero_iff (exp : SecExp spec em) :
--     exp.advantage = 0 ↔ [⊥ | exp.exec exp.main] = 1 := by
--   simp [SecExp.advantage, tsub_eq_zero_iff_le]

-- @[simp]
-- lemma advantage_eq_one_iff (exp : SecExp spec em) :
--     exp.advantage = 1 ↔ [⊥ | exp.exec exp.main] = 0 := by
--   rw [SecExp.advantage, ← probEvent_true, probFailure_eq_sub_probEvent,
--     tsub_eq_zero_iff_le, one_le_probEvent_iff]

-- end advantage

-- end SecExp

-- -- noncomputable def SecExp.advantage {ι : Type} {spec : OracleSpec ι} {σ : Type}
-- --     (exp : SecExp spec σ) (p : σ → Bool) : ℝ≥0∞ :=
-- --   [λ (x, s) ↦ x && p s | exp.exec exp.main]

-- -- noncomputable def SecExp.advantage {ι : Type} {spec : ℕ → OracleSpec ι} (exp : SecExp spec)
-- --     (n : ℕ) : ℝ≥0∞ :=
-- --   [= true | exp.exec n (exp.main n)]

-- -- def SecExp.almostNever {ι : Type} {spec : ℕ → OracleSpec ι} (exp : SecExp spec) : Prop :=
-- --   negligible exp.advantage


-- -- structure SecExp {ι : Type} (spec : ℕ → OracleSpec ι)
-- --     extends OracleAlg spec where
-- --   main (n : ℕ) : OracleComp (spec n) Bool

-- namespace SecExp

-- -- variable {ι : Type} {spec : ℕ → OracleSpec ι} {α β : Type}

-- -- noncomputable def advantage (exp : SecExp spec) (n : ℕ) : ℝ≥0∞ :=
-- --     [= true | exp.exec n (exp.main n)]



-- -- lemma advantage_eq (exp : SecExp spec α) :
-- --     exp.advantage = [= true | exp.exec (exp.inpGen >>= exp.main)] := rfl

-- -- @[simp]
-- -- lemma advantage_eq_one_iff (exp : SecExp spec α) : exp.advantage = 1 ↔
-- --     false ∉ (exp.exec (exp.inpGen >>= exp.main)).support := by
-- --   simp only [advantage_eq, probOutput_eq_one_iff, OracleAlg.exec_bind, support_bind,
-- --     Set.subset_singleton_iff, Set.mem_iUnion, exists_prop, Prod.exists, forall_exists_index,
-- --     and_imp, Bool.forall_bool, imp_false, implies_true, and_true, not_exists, not_and]

-- -- @[simp]
-- -- lemma advantage_eq_zero_iff (exp : SecExp spec α) : exp.advantage = 0 ↔
-- --     true ∉ (exp.exec (exp.inpGen >>= exp.main)).support := by
-- --   rw [advantage_eq, probOutput_eq_zero_iff]

-- -- @[simp]
-- -- lemma advantage_pos_iff (exp : SecExp spec α) : 0 < exp.advantage ↔
-- --     true ∈ (exp.exec (exp.inpGen >>= exp.main)).support := by
-- --   rw [pos_iff_ne_zero, ne_eq, advantage_eq_zero_iff, not_not]

-- end SecExp
