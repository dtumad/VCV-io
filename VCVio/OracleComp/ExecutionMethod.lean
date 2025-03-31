/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Constructions

/-!
# Executing Monads as Probabalistic Computations

This file defines a structure `ExecutionMethod spec m` to provide a way to specify how to
run a monadic computation as a `ProbComp` (and in particular get probability distributions on
outputs of the computation).
Definitions like `SignatureAlg` extend this to allow them to be defined over arbitrary monads.
This means that definitions like "IND-CPA secure" are always *relative* to the execution method.

`ExecutionMethod.default` handles the case where `spec := probSpec`, in which case the
"execution function" is just `id`.
-/

universe u v w

/-- An `ExecutionMethod m` provides a way to map computations in the monad `m` into `ProbComp`.
In particular it allows computations in `m` -/
structure ExecutionMethod (m : Type u → Type v) where
    exec {α : Type u} : m α → ProbComp α
    lift_probComp {α : Type u} : ProbComp α → m α
    exec_lift_probComp {α : Type u} (px : ProbComp α) :
      exec (lift_probComp px) = px

namespace ExecutionMethod

/-- Execute a computation in `ProbComp` via `ProbComp`, by using the identity function. -/
@[simp] protected def default : ExecutionMethod ProbComp where
  exec := id
  lift_probComp := id
  exec_lift_probComp _ := rfl

-- /-- Run a computation `oa` using a given implementation `impl` of its oracles -/
-- def exec [AlternativeMonad m] [LawfulAlternative m] {α : Type v}
--     (impl : ExecutionMethod spec m) (oa : OracleComp spec α) : ProbComp α :=
--   impl.exec_as_probComp (simulateQ impl.toQueryImpl oa)

-- @[simp] lemma exec_def [AlternativeMonad m] [LawfulAlternative m] {α : Type v}
--     (impl : ExecutionMethod spec m) (oa : OracleComp spec α) :
--     impl.exec oa = impl.exec_as_probComp (simulateQ impl.toQueryImpl oa) := rfl

-- @[simp] lemma exec_default {α : Type} [AlternativeMonad m] [LawfulAlternative m]
--     (oa : OracleComp unifSpec α) : ExecutionMethod.default.exec oa = oa := by
--   simp only [ExecutionMethod.default, exec_def, idOracle.simulateQ_eq, id_eq]

end ExecutionMethod
