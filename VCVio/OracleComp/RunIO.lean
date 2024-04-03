/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.OracleComp
import VCVio.CryptoConstructions.OneTimePad

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

/-- Represent an `OracleComp` via the `IO` monad, allowing actual execution. -/
protected def runIO {α : Type} : OracleComp unifSpec α → IO α
  | pure' α x => return x
  | query_bind' i _ α oa => do let u ← IO.rand 0 i; (oa u).runIO


private def lawLargeNumsTest (trials : ℕ) : IO Unit := do
  let xs ← (replicate $[0..4] trials).runIO
  IO.println ("Num 0s: " ++ toString (xs.toList.count 0))
  IO.println ("Num 1s: " ++ toString (xs.toList.count 1))
  IO.println ("Num 2s: " ++ toString (xs.toList.count 2))
  IO.println ("Num 3s: " ++ toString (xs.toList.count 3))
  IO.println ("Num 4s: " ++ toString (xs.toList.count 4))

#eval lawLargeNumsTest 2000

private def testOTP {n : ℕ} (m : Vector Bool n) : IO Unit := do
  IO.println ("Initial Message: " ++ toString m.toList)
  let k ← ((oneTimePad n).exec <| (oneTimePad n).keygen ()).runIO
  IO.println ("Key: " ++ toString k.toList)
  let σ ← ((oneTimePad n).exec <| (oneTimePad n).encrypt m k).runIO
  IO.println ("Ciphertext: " ++ toString σ.toList)
  let m' ← ((oneTimePad n).exec <| (oneTimePad n).decrypt σ k).runIO
  IO.println ("Final Message: " ++ toString m'.toList)

#eval testOTP (Vector.replicate 100 true)

end OracleComp
