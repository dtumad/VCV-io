/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import ToMathlib.Control.FreeMonad
import ToMathlib.Control.WriterT
import ToMathlib.Control.AlternativeMonad
import ToMathlib.Control.OptionT
import Mathlib.Control.Lawful
import VCVio.OracleComp.OracleSpec
import ToMathlib.PFunctor.Basic

/-!
# Computations with Oracle Access

A value `oa : OracleComp spec α` represents a computation with return type `α`,
with access to any of the oracles specified by `spec : OracleSpec`.
Returning a value `x` corresponds to the computation `pure' α x`.
The computation `queryBind' i t α ou` represents querying the oracle corresponding to index `i`
on input `t`, getting a result `u : spec.range i`, and then running `ou u`.
We also allow for a `failure'` operation for quitting out.
These operations induce `Monad` and `Alternative` instances on `OracleComp spec`.

`pure' α a` gives a monadic `pure` operation, while a more general `>>=` operator
is derived by induction on the first computation (see `OracleComp.bind`).
This importantly allows us to define a `LawfulMonad` instance on `OracleComp spec`,
which isn't possible if a general bind operator is included in the main syntax.

We also define simple operations like `coin : OracleComp coinSpec Bool` for flipping a fair coin,
and `$[0..n] : ProbComp (Fin (n + 1))` for selecting from an inclusive range.

Note that the monadic structure on `OracleComp` exists only for a fixed `OracleSpec`,
so it isn't possible to combine computations where one has a superset of oracles of the other.
We later introduce a set of type coercions that mitigate this for most common cases,
such as calling a computation with `spec` as part of a computation with `spec ++ spec'`.
-/

universe u v w z

namespace OracleSpec

/-- An `OracleQuery` to one of the oracles in `spec`, bundling an index and the input to
use for querying that oracle, implemented as a dependent pair.
Implemented as a functor with the oracle output type as the constructor result. -/
inductive OracleQuery {ι : Type u} (spec : OracleSpec.{u,v} ι) : Type v → Type (max u v)
  | query (i : ι) (t : spec.domain i) : OracleQuery spec (spec.range i)

structure OracleQuery' {ι : Type u} (spec : OracleSpec.{u,v} ι) where
  query ::
  i : ι
  t : spec.domain i

namespace OracleQuery

variable {ι : Type u} {spec : OracleSpec ι} {α β : Type v}

def defaultOutput [∀ i, Inhabited (spec.range i)] : (q : OracleQuery spec α) → α
  | query i t => default

def index : (q : OracleQuery spec α) → ι | query i t => i

@[simp] lemma index_query (i : ι) (t : spec.domain i) : (query i t).index = i := rfl

def input : (q : OracleQuery spec α) → spec.domain q.index | query i t => t

@[simp] lemma input_query (i : ι) (t : spec.domain i) : (query i t).input = t := rfl

@[simp]
lemma range_index : (q : OracleQuery spec α) → spec.range q.index = α | query i t => rfl

lemma eq_query_index_input : (q : OracleQuery spec α) →
    q = q.range_index ▸ OracleQuery.query q.index q.input | query i t => rfl

def rangeDecidableEq [spec.DecidableEq] : OracleQuery spec α → DecidableEq α
  | query i t => inferInstance

def rangeFintype [spec.FiniteRange] : OracleQuery spec α → Fintype α
  | query i t => inferInstance

def rangeInhabited [spec.FiniteRange] : OracleQuery spec α → Inhabited α
  | query i t => inferInstance

instance isEmpty : IsEmpty (OracleQuery []ₒ α) where false | query i t => i.elim

instance [hι : DecidableEq ι] [hd : ∀ i, DecidableEq (spec.domain i)] {α : Type u} :
    DecidableEq (OracleQuery spec α)
  | query i t => λ q ↦ match hι i q.index with
    | isTrue h => by
        have : q = query i (h ▸ q.input) := by
          refine q.eq_query_index_input.trans (eq_of_heq (eqRec_heq_iff_heq.2 ?_))
          congr
          · exact h.symm
          · exact HEq.symm (eqRec_heq (Eq.symm h) q.input)
        rw [this, query.injEq]
        exact hd i t _
    | isFalse h => isFalse λ h' ↦ h (congr_arg index h')

end OracleQuery

-- Put `query` in the main `OracleSpec` namespace
export OracleQuery (query)

/-- `PFunctor` corresponding to querying from oracles in `spec`. -/
def toPFunctor {ι : Type u} (spec : OracleSpec.{u,v} ι) : PFunctor where
  A := (i : ι) × spec.domain i
  B := fun q => spec.range q.1

def lift_toPFunctorA {ι : Type u} (spec : OracleSpec.{u,v} ι) {α : Type v}
    (q : OracleQuery spec α) : spec.toPFunctor.A := ⟨q.index, q.input⟩

end OracleSpec
