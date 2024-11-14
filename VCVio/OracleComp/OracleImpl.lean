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
  baseSimOracle : spec →[σ]ₛₒ unifSpec
  init_state : σ

def OracleImpl.exec {ι : Type} {spec : OracleSpec ι} {α σ : Type}
    (impl : OracleImpl spec σ) (oa : OracleComp (unifSpec ++ₒ spec) α) : ProbComp (α × σ) :=
  let so := (idOracle ++ₛₒ impl.baseSimOracle).maskState <| Equiv.punitProd σ
  simulate so impl.init_state oa

def OracleImpl.exec' {ι : Type} {spec : OracleSpec ι} {α σ : Type}
    (impl : OracleImpl spec σ) (oa : OracleComp (unifSpec ++ₒ spec) α) : ProbComp α :=
  let so := (idOracle ++ₛₒ impl.baseSimOracle).maskState <| Equiv.punitProd σ
  simulate' so impl.init_state oa

namespace OracleImpl

def emptyImpl : OracleImpl []ₒ Unit where
  baseSimOracle := unifOracle
  init_state := ()

end OracleImpl
