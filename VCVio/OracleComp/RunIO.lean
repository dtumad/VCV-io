/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.OracleComp
-- import VCVio.OracleComp.Constructions.Replicate
-- import VCVio.OracleComp.Constructions.UniformSelect

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
    (query_map := fun (query i _) ↦ do
      let x ← IO.rand 0 i
      if h : x < i + 1 then return ⟨x, h⟩ else
        -- This should never happen in practice. Would be nice not to need
        throw (IO.Error.illegalOperation 0 "IO.rand returned out of bounds"))

/-- Automatic lifting of probabalistic computations into `IO`. -/
instance : MonadLift ProbComp IO where
  monadLift := OracleComp.runIO

example : IO (ℕ × ℕ) := do
  let x ← IO.rand 0 1618
  let y ← IO.rand 0 3141
  let z := x + y
  IO.println z
  return (x, y)

end OracleComp
