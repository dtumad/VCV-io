/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Data.Fintype.Card
import ToMathlib.PFunctor.Basic

/-!
# Specifications of Available Oracles

This file defines a type `OracleSpec` to represent a set of available oracles.
The available oracles are all indexed by some (potentially infinite) indexing set `ι`,
and for each index `i` a pair of types `domain i` and `range i`.

We also define a number of basic oracle constructions:
* `T →ₒ U`: Access to a single oracle with given input and output
* `coinSpec`: A single oracle for flipping a coin
* `unifSpec`: A family of oracles for selecting from `[0..n]` for any `n`
-/

universe u u' v w

/-- Oracles are specified by a polynomial functor, where `A` is the index/input of the oracle,
and `B` gives the output type of the oracle for a given index.
dt: should we actually have this as an alias? Could in theory drop it completely. -/
abbrev OracleSpec := PFunctor

example : Inhabited OracleSpec := inferInstance --As (Inhabited (PFunctor))

abbrev OracleSpec.domain (spec : OracleSpec) : Type _ := spec.A

/-- Type of the range for calls to the oracle corresponding to index `i`. -/
abbrev OracleSpec.range (spec : OracleSpec) (i : spec.A) := spec.B i

abbrev emptySpec := PFunctor.zero
notation "[]ₒ" => PFunctor.zero

@[inline, reducible]
def coinSpec : OracleSpec.{0,0} := Unit →ₒ Bool

-- Nicer than uniform selection but worse computability.
-- Could just throw errors running if no selectable type exists.
def unifSpec' : OracleSpec.{u+1,u} where
  A := Type u
  B a := a

/-- Access to oracles for uniformly selecting from `Fin (n + 1)` for arbitrary `n : ℕ`.
By adding `1` to the index we avoid selection from the empty type `Fin 0 ≃ empty`.-/
@[inline, reducible] def unifSpec : OracleSpec.{0,0} where
  A := ℕ
  B n := Fin (n + 1)

/-- TODO: should or shouldn't we switch to this. Compare to `(· + m) <$> $[0..n]`.
Select uniformly from a range (not starting from zero).-/
@[inline, reducible] def probSpec : OracleSpec.{0,0} where
  A := ℕ × ℕ
  B r := Fin (r.2 + 1)
