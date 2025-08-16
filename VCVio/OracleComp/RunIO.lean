/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.OracleComp

/-!
# Executing Computations

This file defines a function `runIO` for executing a computation via the `IO` monad.

The semantics mirror `evalDist` in that the oracle will respond uniformly at random,
however we need to limit the oracle set to `unifSpec` to get computability of the function.
In particular we can't choose randomly from arbitrary types.
Usually it's possible to reduce to this anyway using `SelectableType` instances (see `unifOracle`).
-/

open OracleSpec

namespace OracleComp

/-- Represent an `OracleComp` via the `IO` monad, allowing actual execution.
NOTE: `OracleComp` as currently defined doesn't allow specialized error messaging.
Changing this would just require adding a `String` to the `failure` constructor -/
protected def runIO {α : Type} (oa : ProbComp α) : IO α :=
  PFunctor.FreeM.mapM (fun n => Fin.ofNat (n + 1) <$> (IO.rand 0 n).toIO) oa

/-- Automatic lifting of probabalistic computations into `IO`. -/
instance : MonadLift ProbComp IO where
  monadLift := OracleComp.runIO

def test1 : IO (ℕ × ℕ × ℕ) := do
  let x ← $[0..1618]
  let y ← $[0..3141]
  return (x, y, x + y)

def test2 (n : ℕ) : IO (List ℕ) :=
  match n with
  | 0 => return []
  | n + 1 => do
      let x ← $[0..10]
      let xs ← test2 n
      return x :: xs

-- #eval test1
-- #eval test2 100

end OracleComp
