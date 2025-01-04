/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import ToMathlib.FreeMonad
import VCVio.OracleComp.OracleSpec
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

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

universe u v w

open OracleSpec

/-- An `OracleQuery` to one of the oracles in `spec`, bundling an index and the input to
use for querying that oracle, implemented as a dependent pair.
Implemented as a functor with the oracle output type as the constructor result. -/
inductive OracleQuery {ι : Type u} (spec : OracleSpec.{u,v,v} ι) : Type v → Type (max u (v + 1))
  | query (i : ι) : (t : spec.domain i) → OracleQuery spec (spec.range i)

namespace OracleQuery

section Defs

variable {ι : Type u} {spec : OracleSpec ι} {α : Type v}

def defaultOutput [h : spec.FiniteRange] : (q : OracleQuery spec α) → α
  | query i t => default

def index : (q : OracleQuery spec α) → ι
  | query i t => i

def input : (q : OracleQuery spec α) → spec.domain q.index
  | query i t => t

def rangeFintype [spec.FiniteRange] : OracleQuery spec α → Fintype α
  | query i t => inferInstance

def rangeInhabited [spec.FiniteRange] : OracleQuery spec α → Inhabited α
  | query i t => inferInstance

def rangeDecidableEq [spec.DecidableSpec] : OracleQuery spec α → DecidableEq α
  | query i t => inferInstance

instance isEmpty : IsEmpty (OracleQuery []ₒ α) where
  false | query i t => i.elim

end Defs

end OracleQuery

/-- `OracleComp spec α` represents computations with oracle access to oracles in `spec`,
where the final return value has type `α`.
The basic computation is just an `OracleQuery`, augmented with `pure` and `bind` by `FreeMonad`,
and `failure` is also added after by the `OptionT` transformer.

In practive computations in `OracleComp spec α` have have one of three forms:
* `return x` to succeed with some `x : α` as the result.
* `do u ← query i t; oa u` where `oa` is a continutation to run with the query result
* `failure` which terminates the computation early
See `OracleComp.inductionOn` for an explicit induction principle. -/
def OracleComp {ι : Type u} (spec : OracleSpec.{u,v,v} ι) :
    Type v → Type (max (max u (v + 1)) (v + 1)) :=
  OptionT (FreeMonad (OracleQuery spec))

/-- Simplified notation for computations with no oracles besides random inputs. -/
abbrev ProbComp := OracleComp unifSpec

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α β : Type v}

export OracleQuery (query)

instance : Monad (OracleComp spec) := OptionT.instMonad
instance : LawfulMonad (OracleComp spec) := instLawfulMonadOptionT_mathlib _
instance : Inhabited (OracleComp spec α) := Plausible.Testable.instInhabitedOptionTOfPure

/-- Lift a query by first lifting to the free moand and then to the option. -/
def lift (q : OracleQuery spec α) : OracleComp spec α :=
  OptionT.lift (FreeMonad.lift q)

/-- Automatically coerce an `OracleQuery spec α` to an `OracleComp spec α`. -/
instance : MonadLift (OracleQuery spec) (OracleComp spec) where
  monadLift := lift

/-- Lift a function on oracle queries to one on oracle computations. -/
instance : MonadFunctor (OracleQuery spec) (OracleComp spec) where
  monadMap f := (OptionT.instMonadFunctor).monadMap
    ((FreeMonad.instMonadFunctor).monadMap f)

instance : Alternative (OracleComp spec) := OptionT.instAlternative

lemma lift_query_def (i : ι) (t : spec.domain i) :
    (query i t : OracleComp spec (spec.range i)) = OptionT.lift (FreeMonad.lift ⟨i, t⟩) := rfl

@[simp] lemma failure_bind (ob : α → OracleComp spec β) : failure >>= ob = failure := rfl

@[simp] lemma map_failure (f : α → β) : f <$> (failure : OracleComp spec α) = failure := rfl

@[simp] lemma failure_seq (ob : OracleComp spec α) :
    (failure : OracleComp spec (α → β)) <*> ob = failure := rfl

protected lemma bind_congr {oa oa' : OracleComp spec α} {ob ob' : α → OracleComp spec β}
    (h : oa = oa') (h' : ∀ x, ob x = ob' x) : oa >>= ob = oa' >>= ob' :=
  h ▸ (congr_arg (λ ob ↦ oa >>= ob) (funext h'))

/-- `coin` is the computation representing a coin flip, given a coin flipping oracle. -/
@[reducible, inline]
def coin : OracleComp coinSpec Bool := @query _ coinSpec () ()

/-- `$[0..n]` is the computation choosing a random value in the given range, inclusively.
By making this range inclusive we avoid the case of choosing from the empty range. -/
@[reducible, inline]
def uniformFin (n : ℕ) : ProbComp (Fin (n + 1)) := @query _ unifSpec n ()

notation "$[0.." n "]" => uniformFin n

example : ProbComp ℕ := do
  let x ← $[0..31415]; let y ← $[0..16180]
  return x + 2 * y


@[simp]
lemma guard_eq {ι : Type} {spec : OracleSpec ι} (p : Prop) [Decidable p] :
    (guard p : OracleComp spec Unit) = if p then pure () else failure := rfl

-- /-- Total number of queries in a computation across all possible execution paths.
-- Can be a helpful alternative to `sizeOf` when proving recursive calls terminate. -/
-- def totalQueries [spec.FiniteRange] {α : Type u} : (oa : OracleComp spec α) → ℕ
--   | queryBind' _ _ _ oa => 1 + ∑ u, totalQueries (oa u) | _ => 0

/-- Nicer induction rule for `OracleComp` that uses monad notation.
Allows inductive definitions on compuations by considering the three cases:
* `return x` / `pure x` for any `x`
* `do let u ← query i t; oa u` (with inductive results for `oa u`)
* `failure`
See `oracleComp_emptySpec_equiv` for an example of using this in a proof.

If the final result needs to be a `Type` and not a `Prop`, see `OracleComp.construct`. -/
@[elab_as_elim]
protected def inductionOn {C : OracleComp spec α → Prop}
    (pure : (a : α) → C (pure a))
    (query_bind : (i : ι) → (t : spec.domain i) →
      (oa : spec.range i → OracleComp spec α) → (∀ u, C (oa u)) → C (query i t >>= oa))
    (failure : C failure) (oa : OracleComp spec α) : C oa :=
  FreeMonad.inductionOn (Option.rec failure pure)
    (λ q ↦ match q with | query i t => query_bind i t) oa

@[elab_as_elim]
protected def induction {C : OracleComp spec α → Prop}
    (oa : OracleComp spec α) (pure : (a : α) → C (pure a))
    (query_bind : (i : ι) → (t : spec.domain i) →
      (oa : spec.range i → OracleComp spec α) → (∀ u, C (oa u)) → C (query i t >>= oa))
    (failure : C failure) : C oa :=
  FreeMonad.inductionOn (Option.rec failure pure)
    (λ q ↦ match q with | query i t => query_bind i t) oa

section construct

/-- NOTE: if `inductionOn` could work with `Sort u` instead of `Prop` we wouldn't need this,
not clear to me why lean doesn't like unifying the `Prop` and `Type` cases. -/
-- @[elab_as_elim]
-- protected def construct {C : OracleComp spec α → Type v}
--     (pure : (a : α) → C (pure a))
--     (query_bind : {β : Type u} → (q : OracleQuery spec β) →
--       (oa : β → OracleComp spec α) → ((u : β) → C (oa u)) → C (q >>= oa))
--     (failure : C failure) (oa : OracleComp spec α) : C oa :=
--   FreeMonad.construct (Option.rec failure pure) query_bind oa

-- /-- Version of `construct` with automatic induction on the `query` in when defining the
-- `query_bind` case. Can be useful as it constrains the final output type more. -/
@[elab_as_elim]
protected def construct {C : OracleComp spec α → Type w}
    (pure : (a : α) → C (pure a))
    (query_bind : (i : ι) → (t : spec.domain i) →
      (oa : spec.range i → OracleComp spec α) →
      ((u : spec.range i) → C (oa u)) → C (query i t >>= oa))
    (failure : C failure) (oa : OracleComp spec α) : C oa :=
  FreeMonad.construct (Option.rec failure pure)
    (λ q ↦ match q with | query i t => query_bind i t) oa

variable {C : OracleComp spec α → Type w}
  (h_pure : (a : α) → C (pure a))
  (h_query_bind : (i : ι) → (t : spec.domain i) →
      (oa : spec.range i → OracleComp spec α) →
      ((u : spec.range i) → C (oa u)) → C (query i t >>= oa))
  (h_failure : C failure) (oa : OracleComp spec α)

@[simp]
lemma construct_pure (x : α) :
    OracleComp.construct h_pure h_query_bind h_failure (pure x) = h_pure x := rfl

@[simp]
lemma construct_query_bind (i : ι) (t : spec.domain i) (oa : spec.range i → OracleComp spec α) :
    OracleComp.construct h_pure h_query_bind h_failure ((query i t : OracleComp spec _) >>= oa) =
      h_query_bind i t oa (λ u ↦ OracleComp.construct h_pure h_query_bind h_failure (oa u)) := rfl

@[simp]
lemma construct_failure :
    OracleComp.construct h_pure h_query_bind h_failure failure = h_failure := rfl

-- @[simp]
-- lemma construct_query (i : ι) (t : spec.domain i) :
--     OracleComp.construct h_pure h_query_bind h_failure (query i t : OracleComp spec _) =
--       h_query_bind i t _ _

end construct

section mapM

/-- Implement all queries in a computation using some other monad `m`,
preserving the pure and bind operations, giving a computation in the new monad.
The function `qm` specifies how to replace the queries in the computation,
and `fail` is used whenever `failure` is encountered. -/
protected def mapM {m : Type v → Type w} [Monad m]
    (fail : {α : Type v} → m α)
    (qm : {α : Type v} → OracleQuery spec α → m α)
    (oa : OracleComp spec α) : m α :=
  OracleComp.construct pure (λ i t _ r ↦ qm (query i t) >>= r) fail oa

variable {m : Type v → Type w} [Monad m]
  (fail : {α : Type v} → m α) (qm : {α : Type v} → OracleQuery spec α → m α)

@[simp]
lemma mapM_pure (x : α) :
    (pure x : OracleComp spec α).mapM fail qm = pure x := rfl

@[simp]
lemma mapM_bind [LawfulMonad m] (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (oa >>= ob).mapM fail qm = oa.mapM fail qm >>= λ x ↦ (ob x).mapM fail qm := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp only [pure_bind, mapM_pure]
  | query_bind q oa h => sorry
  | failure => sorry

@[simp]
lemma mapM_liftM [LawfulMonad m] (q : OracleQuery spec α) :
    (q : OracleComp spec α).mapM fail qm = qm q :=
  match q with | query i t => by simp only [OracleComp.mapM, OracleComp.construct,
    FreeMonad.construct, bind_pure]

@[simp]
lemma mapM_query [LawfulMonad m] (i : ι) (t : spec.domain i) :
    (query i t : OracleComp spec _).mapM fail qm = qm (query i t) := by
  rw [mapM_liftM]

@[simp]
lemma mapM_failure : (failure : OracleComp spec α).mapM fail qm = fail := rfl

end mapM

section noConfusion

variable (i : ι) (t : spec.domain i) (u : spec.range i) (x : α)
  (ou : spec.range i → OracleComp spec α)
  (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β)

/-- Returns `true` for computations that don't query any oracles or fail, else `false` -/
def isPure {α : Type v} : OracleComp spec α → Bool
  | FreeMonad.pure x => Option.isSome x
  | _ => false

/-- Returns `true` for computations that fail else `false`. -/
def isFailure {α : Type v} : OracleComp spec α → Bool
  | FreeMonad.pure x => Option.isNone x
  | _ => false

-- @[simp] lemma isPure_pure : isPure (pure x : OracleComp spec α) = true := rfl
-- @[simp] lemma isPure_query_bind : isPure (query i t >>= ou) = false := rfl
-- @[simp] lemma isPure_failure : isPure (failure : OracleComp spec α) = false := rfl
-- @[simp] lemma isFailure_pure (spec : OracleSpec ι) (x : α) :
--     isFailure (pure x : OracleComp spec α) = false := rfl
-- @[simp] lemma isFailure_query_bind (i : ι) (t : spec.domain i)
--     (oa : spec.range i → OracleComp spec β) : isFailure (query i t >>= oa) = false := rfl
-- @[simp] lemma isFailure_failure : isFailure (failure : OracleComp spec α) = true := rfl

-- @[simp] lemma pure_ne_query : pure u ≠ query i t := sorry --OracleComp.noConfusion
-- @[simp] lemma query_ne_pure : query i t ≠ pure u := sorry --OracleComp.noConfusion
-- @[simp] lemma pure_ne_query_bind : pure x ≠ query i t >>= ou := sorry --OracleComp.noConfusion
-- @[simp] lemma query_bind_ne_pure : query i t >>= ou ≠ pure x := sorry --OracleComp.noConfusion
-- @[simp] lemma pure_ne_failure :
--(pure x : OracleComp spec α) ≠ failure := sorry --OracleComp.noConfusion
-- @[simp] lemma failure_ne_pure : failure ≠ (pure x : OracleComp spec α) :=
--sorry --OracleComp.noConfusion
-- @[simp] lemma query_ne_failure : query i t ≠ failure := sorry --OracleComp.noConfusion
-- @[simp] lemma failure_ne_query : failure ≠ query i t := sorry --OracleComp.noConfusion
-- @[simp] lemma failure_ne_query_bind : failure ≠ query i t >>= ou :=
  --sorry --OracleComp.noConfusion
-- @[simp] lemma query_bind_ne_failure : query i t >>= ou ≠ failure :=
  --sorry --OracleComp.noConfusion

-- lemma exists_eq_of_isPure {oa : OracleComp spec α} (h : isPure oa) :  ∃ x, oa = pure x := by
--   induction oa using OracleComp.inductionOn with
--   | pure => apply exists_apply_eq_apply' | query_bind => simp at h | failure => simp at h
-- lemma eq_failure_of_isFailure {oa : OracleComp spec α} (h : isFailure oa) : oa = failure := by
--   induction oa using OracleComp.inductionOn with
--   | pure => simp at h | query_bind => simp at h | failure => rfl

end noConfusion

section inj

@[simp] lemma pure_inj (x y : α) : (pure x : OracleComp spec α) = pure y ↔ x = y :=
  sorry --⟨λ h ↦ OracleComp.noConfusion h (λ _ hx ↦ eq_of_heq hx), λ h ↦ h ▸ rfl⟩

@[simp] lemma query_inj (i : ι) (t t' : spec.domain i) : query i t = query i t' ↔ t = t' :=
  sorry --⟨λ h ↦ OracleComp.noConfusion h (λ _ ht _ _ ↦ eq_of_heq ht), λ h ↦ h ▸ rfl⟩

@[simp]
lemma queryBind_inj' (i i' : ι) (t : spec.domain i) (t' : spec.domain i')
    (oa : spec.range i → OracleComp spec α) (oa' : spec.range i' → OracleComp spec α) :
    (query i t : OracleComp spec _) >>= oa =
        (query i' t' : OracleComp spec _) >>= oa' ↔
      ∃ h : i = i', h ▸ t = t' ∧ h ▸ oa = oa' := by
  sorry
  -- refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  -- · rw [← queryBind'_eq_queryBind, ← queryBind'_eq_queryBind] at h
  --   refine OracleComp.noConfusion h ?_
  --   rintro rfl ⟨rfl⟩ _ ⟨rfl⟩
  --   exact ⟨rfl, rfl, rfl⟩
  -- · obtain ⟨rfl, rfl, rfl⟩ := h; rfl

lemma queryBind_inj (i : ι) (t t' : spec.domain i) (oa oa' : spec.range i → OracleComp spec α) :
    (query i t : OracleComp spec _) >>= oa =
      (query i t' : OracleComp spec _) >>= oa' ↔ t = t' ∧ oa = oa' :=
  by simp only [queryBind_inj', exists_const]

/-- If the final output type of a computation has decidable equality,
then computations themselves have decidable equality. -/
protected instance instDecidableEq [spec.DecidableSpec] [spec.FiniteRange]
    [DecidableEq ι] [h : DecidableEq α] : DecidableEq (OracleComp spec α) := sorry
  -- | pure' _ x, pure' _ x' => by simpa [pure_inj x x'] using h x x'
  -- | pure' _ _, queryBind' _ _ _ _ => by simpa using instDecidableFalse
  -- | queryBind' _ _ _ _, pure' _ x => by simpa using instDecidableFalse
  -- | failure' _, failure' _ => by simpa using instDecidableTrue
  -- | failure' _, pure' _ _ => by simpa using instDecidableFalse
  -- | pure' _ _, failure' _ => by simpa using instDecidableFalse
  -- | failure' _, queryBind' _ _ _ _ => by simpa using instDecidableFalse
  -- | queryBind' _ _ _ _, failure' _ => by simpa using instDecidableFalse
  -- | queryBind' i t _ oa, queryBind' i' t' _ oa' => by
  --   by_cases hi : i = i'
  --   · induction hi; simp
  --     suffices Decidable (oa = oa') from inferInstance
  --     suffices Decidable (∀ u, oa u = oa' u) from decidable_of_iff' _ funext_iff
  --     suffices ∀ u, Decidable (oa u = oa' u) from Fintype.decidableForallFintype
  --     exact λ u ↦ OracleComp.instDecidableEq (oa u) (oa' u)
  --   · simpa [hi] using instDecidableFalse

end inj

@[simp]
lemma bind_eq_pure_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β) :
    oa >>= ob = pure y ↔ ∃ x : α, oa = pure x ∧ ob x = pure y := sorry --by
  -- refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  -- · match oa with
  --   | pure' _ x => exact ⟨x, rfl, h⟩
  --   | queryBind' i t _ oa => simp at h
  --   | failure' _ => simp at h
  -- · obtain ⟨x, hxa, hxb⟩ := h
  --   rw [hxa, pure_bind, hxb]

@[simp]
lemma pure_eq_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β) :
    pure y = oa >>= ob ↔ ∃ x : α, oa = pure x ∧ ob x = pure y :=
  eq_comm.trans (bind_eq_pure_iff oa ob y)

alias ⟨_, bind_eq_pure⟩ := bind_eq_pure_iff
alias ⟨_, pure_eq_bind⟩ := pure_eq_bind_iff

/-- Given a computation `oa : OracleComp spec α`, construct a value `x : α`,
by assuming each query returns the `default` value given by the `Inhabited` instance.
Returns `none` if the default path would lead to failure. -/
def defaultResult {ι : Type u} {spec : OracleSpec ι} {α : Type v} [spec.FiniteRange]
    (oa : OracleComp spec α) : Option α :=
  oa.construct some (λ _ _ _ r ↦ r default) none

-- /-- Computations without access to any oracles are equivalent to values of the return type.
-- `toFun` is slightly different than `defaultResult` in that it doesn't recurse at all. -/
-- def oracleComp_emptySpec_equiv (α : Type) : OracleComp []ₒ α ≃ Option α where
--   toFun oa := match oa with
--     | pure' _ x => some x
--     | queryBind' i _ _ _ => PEmpty.elim i
--     | failure' _ => none
--   invFun x := match x with | some x => pure x | none => failure
--   left_inv oa := by induction oa using OracleComp.induction with
--     | pure x => rfl
--     | query_bind i t oa hoa => exact PEmpty.elim i
--     | failure => rfl
--   right_inv x := match x with | some x => rfl | none => rfl

-- NOTE: This should maybe be a `@[simp]` lemma? `apply_ite` can't be a simp lemma in general.
lemma ite_bind (p : Prop) [Decidable p] (oa oa' : OracleComp spec α)
    (ob : α → OracleComp spec β) : ite p oa oa' >>= ob = ite p (oa >>= ob) (oa' >>= ob) :=
  apply_ite (· >>= ob) p oa oa'

end OracleComp
