/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.UniformSelect
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.Constructions.UniformSelect

/-!
# Learning With Errors

This file gives a general definition of the LWE problem. It is parameterized by the following:
- `n`: the dimension of the secret
- `m`: the number of samples
- `p`: the modulus (not necessarily prime)
- `errSamp : ProbComp (Fin p)`: a probabilistic sampling algorithm for the error

(`errSamp` can potentially be replaced with `χ : PMF (Fin p)` instead, to be used with
`evalDistWhen` with non-uniform distributions)

We define the (decision) LWE problem as a security experiment on an oracle that takes as input:
- A matrix `A : Fin m → Fin n → Fin p`
- A vector `b : Fin m → Fin p`, either sampled uniformly at random, or sampled from the LWE
  distribution `s * A + e`, where `s : Fin n → Fin p` is the secret and `e : Fin m → Fin p` has
  every entry sampled from `errSamp`.

The adversary wins if it can correctly guess which case the distribution is.

The search LWE problem instead asks that the adversary given `A` and `b = s * A + e` outputs the
secret `s`.
-/

open OracleComp OracleSpec ENNReal

variable {n m p : ℕ} {errSamp : ProbComp (Fin p)}

/-- The LWE distribution `(A, s * A + e)` -/
def LWE_Distr (n m p : ℕ) [NeZero p] (errSamp : ProbComp (Fin p)) :
    ProbComp (Matrix (Fin n) (Fin m) (Fin p) × Vector (Fin p) m) := do
  let A ←$ᵗ Matrix (Fin n) (Fin m) (Fin p)
  let s ←$ᵗ Vector (Fin p) n
  -- Sampled each entry of `e` independently using `errSamp`
  let e ← (Vector.range m).mapM (fun _ ↦ errSamp)
  let b := A.vecMul s.get + e.get
  return (A, Vector.ofFn b)

/-- The uniform distribution `(A, u)` -/
def LWE_Uniform_Distr (n m p : ℕ) [NeZero p] :
    ProbComp (Matrix (Fin n) (Fin m) (Fin p) × Vector (Fin p) m) := do
  let A ←$ᵗ Matrix (Fin n) (Fin m) (Fin p)
  let u ←$ᵗ Vector (Fin p) m
  return (A, u)

/-- An adversary for the decisional LWE problem. Takes in a pair `(A, b)` and outputs a boolean. -/
def LWE_Adversary (n m p : ℕ) [NeZero p] :=
  Matrix (Fin n) (Fin m) (Fin p) × Vector (Fin p) m → ProbComp Bool

/-- The decisional LWE experiment. If `b = true`, the distribution is LWE, otherwise it is uniform. -/
def LWE_Experiment (n m p : ℕ) [NeZero p] (errSamp : ProbComp (Fin p)) (adv : LWE_Adversary n m p) :
    ProbComp Unit := do
  let b ←$ᵗ Bool
  let distr ← if b then LWE_Distr n m p errSamp else LWE_Uniform_Distr n m p
  let b' ← adv distr
  guard (b' = b)

def LWE_Search_Adversary (n m p : ℕ) [NeZero p] :=
  Matrix (Fin n) (Fin m) (Fin p) × Vector (Fin p) m → ProbComp (Vector (Fin p) n)

def LWE_Search_Experiment (n m p : ℕ) [NeZero p] (errSamp : ProbComp (Fin p))
    (adv : LWE_Search_Adversary n m p) : ProbComp Unit := do
  let A ←$ᵗ Matrix (Fin n) (Fin m) (Fin p)
  let s ←$ᵗ Vector (Fin p) n
  -- Sampled each entry of `e` independently using `errSamp`
  let e ← (Vector.range m).mapM (fun _ ↦ errSamp)
  let b := A.vecMul s.get + e.get
  let s' ← adv (A, Vector.ofFn b)
  guard (s' = s)
