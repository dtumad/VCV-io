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

/-- Represent an `OracleComp` via the `IO` monad, allowing actual execution.
NOTE: `OracleComp` as currently defined doesn't allow specialized error messaging.
Changing this would just require adding a `String` to the `failure` constructor -/
protected def runIO {α : Type} (oa : ProbComp α) : IO α :=
  oa.mapM (fail := throw (IO.userError "Computation failed during execution"))
    (qm := λ (query i _) ↦ IO.rand 0 i) -- Queries become random selection

/-- Automatic lifting of probabalistic computations into `IO`. -/
instance : MonadLift ProbComp IO where
  monadLift := OracleComp.runIO

private def lawLargeNumsTest (trials : ℕ) (die : ℕ) : IO Unit := do
  let n : ℕ := trials * die
  let xs ← replicateTR n $[0..die - 1]
  IO.println ("Rolling " ++ toString n ++ " " ++ toString die ++ "-sided dice:")
  for i in List.range die do
    IO.println <| "▸Num " ++ toString (i + 1) ++ "s: " ++ toString (xs.count i)

#eval (do
  let trials : ℕ ← (100 + ·) <$> $[0..100]
  let die : ℕ ← (4 + ·) <$> $[0..4]
  lawLargeNumsTest trials die : IO Unit)

end OracleComp
