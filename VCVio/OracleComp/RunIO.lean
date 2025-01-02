/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.OracleComp
import VCVio.OracleComp.Constructions.Replicate
import VCVio.OracleComp.Constructions.UniformSelect

/-!
# Executing Computations

This file defines a function `runIO` for executing a computation via the `IO` monad.

The semantics mirror `evalDist` in that the oracle will respond uniformly at random,
however we need to limit the oracle set to `unifSpec` to get computability of the function.
In particular we can't choose randomly from arbitrary types.
Usually it's possible to reduce to this anyway using `SelectableType` instances (see `unifOracle`).

NOTE: `OracleComp.failure` could instead be an error to allow error msg propogation.
-/

open OracleSpec

namespace OracleComp

/-- The type of computation that `runIO` will produce. -/
example : IO ℕ := do
  let x ← IO.rand 2 10
  let y ← IO.rand 100 200
  return (x * y)

/-- Represent an `OracleComp` via the `IO` monad, allowing actual execution.
NOTE: `OracleComp` as currently defined doesn't allow specialized error messaging.
Changing this would just require adding a `String` to the `failure` constructor -/
protected def runIO {α : Type} (oa : ProbComp α) : IO α := by
  induction oa using OracleComp.construct with
  | pure x => exact return x
  | query_bind i t oa r => exact do let u ← IO.rand 0 i; r u
  | failure => exact throw (IO.userError "Computation failed during execution")

private def lawLargeNumsTest (trials : ℕ) (die : ℕ) : IO Unit := do
  let n : ℕ := trials * die
  let xs ← (replicate n $[0..die - 1]).runIO
  IO.println ("Rolling " ++ toString n ++ " " ++ toString die ++ "-sided dice:")
  for i in List.range die do
    IO.println <| "▸Num " ++ toString (i + 1) ++ "s: " ++ toString (xs.count i)

#eval lawLargeNumsTest 200 6

end OracleComp
