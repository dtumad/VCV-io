/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Constructions
import VCVio.OracleComp.Coercions.Append

/-!
# Append Operation for Simulation Oracles

This file defines an operation `SimOracle.append` that takes two simulation oracles `so` and `so'`
from `spec₁` and `spec₂` respectively to a shared target spec `specₜ`,
and constructs a new simulation oracle from `spec₁ ++ spec₂` to `specₜ`.

This operation is also compatible with the `SubSpec` instances involving `OracleSpec.append`.
For example if `oa : OracleComp spec₁ α` is coerced to `↑oa : OracleComp (spec₁ ++ spec₂) α`,
then we have `simulate' (so ++ₛₒ so') ↑oa s = simulate' so oa s.1`, as the additional
oracles from the coercion will never actually be called.

TODO: simp lemmas are not always applied properly, seemingly due to the free `n` variable.
-/

open OracleSpec OracleComp Prod Sum

universe u v w

namespace SimOracle

variable {ι₁ ι₂ ι₃ : Type*} {spec₁ : OracleSpec ι₁}
  {spec₂ : OracleSpec ι₂} {spec₃ : OracleSpec ι₃} {α β γ : Type u}

/-- Given simulation oracles `so` and `so'` with source oracles `spec₁` and `spec₂` respectively,
with the same target oracles `specₜ`, construct a new simulation oracle from `specₜ`,
answering queries to either oracle set with queries to the corresponding simulation oracle.
NOTE: `n` can't be inferred from the explicit parameters, the use case needs to give context -/
def append {m : Type _ → Type _} (so : QueryImpl spec₁ m) (so' : QueryImpl spec₂ m) :
    QueryImpl (spec₁ ++ₒ spec₂) m where impl
  | query (inl i) t => so.impl (query i t)
  | query (inr i) t => so'.impl (query i t)

infixl : 65 " ++ₛₒ " => append

variable {m₁ m₂ n : Type u → Type v} [MonadLift m₁ n] [MonadLift m₂ n]
    (so : QueryImpl spec₁ m₁) (so' : QueryImpl spec₂ m₂)

@[simp] lemma append_apply_inl
    (so : QueryImpl spec₁ n) (so' : QueryImpl spec₂ n) (i : ι₁) (t : spec₁.domain i) :
    (so ++ₛₒ so' : QueryImpl _ n).impl (query (inl i) t) = so.impl (query i t) := rfl

@[simp]
lemma append_apply_inr --{m₁ m₂ n : Type u → Type v} [MonadLift m₁ n] [MonadLift m₂ n]
    (so : QueryImpl spec₁ n) (so' : QueryImpl spec₂ n) (i : ι₂) (t : spec₂.domain i) :
    (so ++ₛₒ so' : QueryImpl _ n).impl (query (inr i) t) = so'.impl (query i t) := rfl

variable [AlternativeMonad n] [LawfulAlternative n] [LawfulMonad n]

-- @[simp]
-- lemma simulateQ_liftComp_append_left [AlternativeMonad m₁] [LawfulMonad m₁]
--     [LawfulMonadLift m₁ n] [LawfulAlternativeLift m₁ n] (oa : OracleComp spec₁ α) :
--     (simulateQ (so ++ₛₒ so') (liftComp oa (spec₁ ++ₒ spec₂)) : n α) =
--       (liftM (simulateQ so oa) : n α) := by
--   induction oa using OracleComp.inductionOn with
--   | pure x => simp
--   | query_bind i t oa hoa =>
--       simp at hoa
--       simp [hoa, append_apply_inl so so', Function.comp_def]
--   | failure => simp

@[simp]
lemma simulateQ_liftComp_append_left' (so : QueryImpl spec₁ n) (so' : QueryImpl spec₂ n)
    (oa : OracleComp spec₁ α) : (simulateQ (so ++ₛₒ so') (liftComp oa (spec₁ ++ₒ spec₂)) : n α) =
      simulateQ so oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind i t oa hoa =>
      simp at hoa
      simp [hoa, append_apply_inl so so', Function.comp_def]
  | failure => simp

-- @[simp]
-- lemma simulate_coe_append_left [AlternativeMonad m₁] [LawfulMonad m₁] [LawfulAlternative m₁]
--     [LawfulMonadLift m₁ n] [LawfulAlternativeLift m₁ n] (oa : OracleComp spec₁ α) :
--     simulateQ (so ++ₛₒ so') (liftM oa) = (liftM (simulateQ so oa) : n α) := by
--   induction oa using OracleComp.inductionOn with
--   | pure x => simp
--   | query_bind i t oa hoa =>
--       simp at hoa
--       simp [hoa, append_apply_inl so so', Function.comp_def]
--   | failure => simp

-- @[simp]
-- lemma simulate_coe_append_right [AlternativeMonad m₂] [LawfulMonad m₂]
--     [LawfulMonadLift m₂ n] [LawfulAlternativeLift m₂ n] (oa : OracleComp spec₂ α) :
--     simulateQ (so ++ₛₒ so') (liftM oa) = (liftM (simulateQ so' oa) : n α) := by
--   induction oa using OracleComp.inductionOn with
--   | pure x => simp
--   | query_bind i t oa hoa =>
--       simp at hoa
--       simp [hoa, append_apply_inr so so', Function.comp_def]
--   | failure => simp


@[simp] lemma liftComp_left_append_left_append_eq
    {m : Type _ → Type _} [AlternativeMonad m]
    (so : QueryImpl spec₁ m)
    (so' : QueryImpl spec₂ m)
    (so'' : QueryImpl spec₃ m)
    (oa : OracleComp (spec₁ ++ₒ spec₂) α) :
    (simulateQ (so ++ₛₒ (so' ++ₛₒ so'' : QueryImpl _ m))
        (OracleComp.liftComp oa (spec₁ ++ₒ (spec₂ ++ₒ spec₃))) : m α) =
      simulateQ (so ++ₛₒ so') oa := by
  sorry

end SimOracle

namespace OracleComp

variable {ι : Type _} {spec : OracleSpec ι} {α β γ : Type _}

/-- Version of `simulateQ` that assumes additional `probComp` oracle. -/
@[reducible] def simulateR  (so : QueryImpl spec ProbComp)
    (oa : OracleComp (unifSpec ++ₒ spec) α) : ProbComp α :=
  simulateQ (idOracle unifSpec ++ₛₒ so) oa

end OracleComp
