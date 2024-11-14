/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Constructions
import VCVio.OracleComp.SimSemantics.Append

/-!
# Implementations of Oracles

This file defines a structure `OracleImpl spec σ` that represents a specification of
how to run the oracles in `spec` using only probabalistic computations.
The type `σ` is the state used in the implementation (e.g. a random oracle's cache).

We implement this a structure so that the types of protocols can extend it,
allowing the main definition to be oracle agnostic.
-/

open OracleSpec OracleComp

/-- An implementation of the oracles in `spec` gives a way to run all the oracles in `spec`.
Allows a computation using `spec` to be simulated in terms of `unifSpec` to produce
a `ProbComp` that can be run with `OracleComp.runIO`.

The types of primitives can extend this to ensure that any oracles used in a protocol
must have some canonical implementation. -/
structure OracleImpl {ι : Type} (spec : OracleSpec ι) (σ : Type) where
  /-- Simulation oracle giving an implementation of the oracles in `spec`. -/
  baseSimOracle : spec →[σ]ₛₒ unifSpec
  init_state : σ

variable {ι : Type} {spec : OracleSpec ι} {σ α β γ : Type}

/-- Run a computation `oa` using a given implementation `impl` of its oracles,
with initial state `s`. Returns both the result and final state.
The computation `oa` is assumed to also have access to uniform selection oracles,
which are simulated by directly forwarding their calls with `idOracle`. -/
def OracleImpl.run (impl : OracleImpl spec σ)
    (oa : OracleComp (unifSpec ++ₒ spec) α) (s : σ) : ProbComp (α × σ) :=
  let so := (idOracle ++ₛₒ impl.baseSimOracle).maskState <| Equiv.punitProd σ
  simulate so s oa

/-- Shorthand for running a computation using the given oracle implementation,
using the initial simulation state specified by the implementation itself. -/
abbrev OracleImpl.exec (impl : OracleImpl spec σ)
    (oa : OracleComp (unifSpec ++ₒ spec) α) : ProbComp (α × σ) :=
  OracleImpl.run impl oa impl.init_state

-- def OracleImpl.exec' (impl : OracleImpl spec σ)
--     (oa : OracleComp (unifSpec ++ₒ spec) α) : ProbComp α :=
--   let so := (idOracle ++ₛₒ impl.baseSimOracle).maskState <| Equiv.punitProd σ
--   simulate' so impl.init_state oa

namespace OracleImpl

@[simp]
lemma exec_pure (impl : OracleImpl spec σ) (x : α) (s : σ) :
    impl.run (return x) s = return (x, s) := rfl

@[simp]
lemma exec_bind (impl : OracleImpl spec σ) (oa : OracleComp (unifSpec ++ₒ spec) α)
    (ob : α → OracleComp (unifSpec ++ₒ spec) β) (s : σ) :
    (impl.run (oa >>= ob) s = do let (x, s') ← impl.run oa s; impl.run (ob x) s') := by
  simp [OracleImpl.run]

-- @[simp]
-- lemma exec_query (impl : OracleImpl spec σ) (i : ℕ ⊕ ι) (t : (unifSpec ++ₒ spec).domain i)
--     (s : σ) : impl.run (query i t) s = sorry := sorry

def emptyImpl : OracleImpl []ₒ Unit where
  baseSimOracle := unifOracle
  init_state := ()

end OracleImpl
