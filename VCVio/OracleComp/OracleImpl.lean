/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Constructions

/-!
# Implementations of Oracles

This file defines a structure `OracleImpl spec σ` that represents a specification of
how to run the oracles in `spec` using only probabalistic computations.
The type `σ` is the state used in the implementation (e.g. a random oracle's cache).

We implement this a structure so that the types of protocols can extend it,
allowing the main definition to be oracle agnostic.

TODO!: re-evaluate this in context of the simulate changes
-/

universe u v w

open OracleSpec OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {em : Type v → Type w}

/-- An implementation of the oracles in `spec` gives a way to run all the oracles in `spec`.
Allows a computation using `spec` to be simulated in terms of `unifSpec` to produce
a `ProbComp` that can be run with `OracleComp.runIO`.
The types of primitives can extend this to ensure that any oracles used in a protocol
must have some canonical implementation. -/
structure ExecutionMethod (spec : OracleSpec ι) (em : Type v → Type w)
    extends QueryImpl spec em where
  exec_as_probComp {α : Type v} : em α → ProbComp α

namespace ExecutionMethod

/-- Run a computation `oa` using a given implementation `impl` of its oracles -/
def exec [AlternativeMonad em] [LawfulAlternative em] {α : Type v}
    (impl : ExecutionMethod spec em) (oa : OracleComp spec α) : ProbComp α :=
  impl.exec_as_probComp (simulateQ impl.toQueryImpl oa)

/-- Implement a computation on `unifSpec` as a `ProbComp` by identity. -/
protected def default : ExecutionMethod unifSpec ProbComp where
  exec_as_probComp := id
  __ := idOracle

end ExecutionMethod
