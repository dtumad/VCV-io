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

/-- An implementation of the oracles in `spec` gives a way to run all the oracles in `spec`.
Allows a computation using `spec` to be simulated in terms of `unifSpec` to produce
a `ProbComp` that can be run with `OracleComp.runIO`.

The types of primitives can extend this to ensure that any oracles used in a protocol
must have some canonical implementation. -/
structure OracleImpl {ι : Type} (spec : OracleSpec ι) (σ : Type) where
  /-- Simulation oracle giving an implementation of the oracles in `spec`. -/
  baseSimOracle : QueryImpl spec (StateT σ (OracleComp unifSpec))
  init_state : σ

section new

variable {ι : Type u} {spec : OracleSpec ι} {m : Type u → Type v}
    [AlternativeMonad m] [LawfulAlternative m] {α : Type u}

structure OracleImpl' (spec : OracleSpec ι) (m : Type u → Type v)
    extends QueryImpl spec m where
  -- How to run the computation. e.g. call `StateT.run` with an empty cache as initial state
  exec_as_probComp {α : Type u} : m α → ProbComp α

-- Execute a computation so you can use `evalDist` to reason about it
def exec (impl : OracleImpl' spec m) (oa : OracleComp spec α) : ProbComp α :=
  impl.exec_as_probComp (simulateQ impl.toQueryImpl oa)

end new

namespace OracleImpl

variable {ι : Type} {spec : OracleSpec ι} {σ α β γ : Type}

/-- Run a computation `oa` using a given implementation `impl` of its oracles,
with initial state `s`. Returns both the result and final state.
The computation `oa` is assumed to also have access to uniform selection oracles,
which are simulated by directly forwarding their calls with `idOracle`. -/
abbrev run (impl : OracleImpl spec σ) (s : σ)
    (oa : OracleComp spec α) : ProbComp (α × σ) :=
  simulate impl.baseSimOracle s oa

abbrev exec (impl : OracleImpl spec σ)
    (oa : OracleComp spec α) : ProbComp (α × σ) :=
  simulate impl.baseSimOracle impl.init_state oa

/-- Impliment an empty set of oracles by eliminating on the empty index to any queries. -/
@[simps] def emptyImpl [∀ i, SelectableType (spec.range i)] : OracleImpl []ₒ Unit where
  baseSimOracle := ⟨liftM⟩ ∘ₛ unifOracle
  init_state := ()

/-- Implement `unifSpec` as `unifSpec` by identity. -/
@[simps] def defaultImpl : OracleImpl unifSpec Unit where
  baseSimOracle := ⟨liftM⟩ ∘ₛ idOracle
  init_state := ()

end OracleImpl
