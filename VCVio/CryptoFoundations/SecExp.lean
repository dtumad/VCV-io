/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.OracleImpl
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

open OracleComp OracleSpec ENNReal Polynomial Prod

/-- A security adversary bundling a computation with a bound on the number of queries it makes,
where the bound is given by a polynomial that is evaluated for each security parameter.
This is useful both for asymptotic security as well as in some concrete security bounds.

Port: We should eventually include polynomial time in this -/
-- structure SecAdv {ι : Type} [DecidableEq ι]
--     (spec : ℕ → OracleSpec ι) (α β : ℕ → Type) where
--   run (n : ℕ) : α n → OracleComp (spec n) (β n)
--   qb (i : ι) : ℕ[X] -- Bound on the number of queries made by adversary.
--   qb_isQueryBound (n : ℕ) (x : α n) :
--     IsQueryBound (run n x) (λ i ↦ (qb i).eval n)

structure SecAdv {ι : Type} [DecidableEq ι]
    (spec : OracleSpec ι) (α β : Type) where
  run : α → OracleComp spec β
  qb : ι → ℕ
  qb_isQueryBound (x : α) : IsQueryBound (run x) (qb)

namespace SecAdv

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

end SecAdv

-- structure SecExp {ι : Type} (spec : ℕ → OracleSpec ι)
--     extends OracleAlg spec where
--   main (n : ℕ) : OracleComp (unifSpec ++ₒ spec n) Bool

-- structure SecExp {ι : Type} (spec : OracleSpec ι) (σ : Type)
--     extends OracleImpl spec σ where
--   main : OracleComp spec Bool

/-- Structure to represent a security experiment. `spec` is the set of oracles available
in the experiment, and the structure extends an oracle implementation for `spec`.
`σ` is the state type for the implementation, and `ρ` is the result type of the expirement.

`is_valid : σ → ρ → Bool` determines if the experiment was succesfull or not.  -/
-- structure SecExp {ι : Type} (spec : OracleSpec ι) (σ ρ : Type)
--     extends OracleImpl spec σ where
--   main : OracleComp spec ρ
--   is_valid : ρ × σ → Prop

structure SecExp {ι : Type} (spec : OracleSpec ι) (σ : Type)
    extends OracleImpl spec σ where
  main : OracleComp spec Unit

noncomputable def SecExp.advantage {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (exp : SecExp spec σ) : ℝ≥0∞ :=
  1 - [⊥ | exp.exec exp.main]

namespace SecExp

variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

@[simp]
lemma advantage_eq_one_iff (exp : SecExp spec σ) :
    exp.advantage = 1 ↔ [⊥ | exp.exec exp.main] = 0 := by
  sorry

end SecExp

-- noncomputable def SecExp.advantage {ι : Type} {spec : OracleSpec ι} {σ : Type}
--     (exp : SecExp spec σ) (p : σ → Bool) : ℝ≥0∞ :=
--   [λ (x, s) ↦ x && p s | exp.exec exp.main]

-- noncomputable def SecExp.advantage {ι : Type} {spec : ℕ → OracleSpec ι} (exp : SecExp spec)
--     (n : ℕ) : ℝ≥0∞ :=
--   [= true | exp.exec n (exp.main n)]

-- def SecExp.almostNever {ι : Type} {spec : ℕ → OracleSpec ι} (exp : SecExp spec) : Prop :=
--   negligible exp.advantage


-- structure SecExp {ι : Type} (spec : ℕ → OracleSpec ι)
--     extends OracleAlg spec where
--   main (n : ℕ) : OracleComp (spec n) Bool

namespace SecExp

-- variable {ι : Type} {spec : ℕ → OracleSpec ι} {α β : Type}

-- noncomputable def advantage (exp : SecExp spec) (n : ℕ) : ℝ≥0∞ :=
--     [= true | exp.exec n (exp.main n)]



-- lemma advantage_eq (exp : SecExp spec α) :
--     exp.advantage = [= true | exp.exec (exp.inpGen >>= exp.main)] := rfl

-- @[simp]
-- lemma advantage_eq_one_iff (exp : SecExp spec α) : exp.advantage = 1 ↔
--     false ∉ (exp.exec (exp.inpGen >>= exp.main)).support := by
--   simp only [advantage_eq, probOutput_eq_one_iff, OracleAlg.exec_bind, support_bind,
--     Set.subset_singleton_iff, Set.mem_iUnion, exists_prop, Prod.exists, forall_exists_index,
--     and_imp, Bool.forall_bool, imp_false, implies_true, and_true, not_exists, not_and]

-- @[simp]
-- lemma advantage_eq_zero_iff (exp : SecExp spec α) : exp.advantage = 0 ↔
--     true ∉ (exp.exec (exp.inpGen >>= exp.main)).support := by
--   rw [advantage_eq, probOutput_eq_zero_iff]

-- @[simp]
-- lemma advantage_pos_iff (exp : SecExp spec α) : 0 < exp.advantage ↔
--     true ∈ (exp.exec (exp.inpGen >>= exp.main)).support := by
--   rw [pos_iff_ne_zero, ne_eq, advantage_eq_zero_iff, not_not]

end SecExp
