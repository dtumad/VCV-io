/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
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

/-- `OracleComp spec α` represents computations with oracle access to oracles in `spec`,
where the final return value has type `α`.

The constructor `pure' α x` allow for returning a pure Lean value `x`,
and `queryBind' i t α ou` allows for querying oracle `i` on input `t`,
calling `ou` on the result of the oracle call.
`failure' α` fails to return but expects to have return type `α`.
We recursively define a more general monadic bind operation later.

NOTE: if we want full universe polymorphism then `OracleSpec` needs that too. -/
inductive OracleComp {ι : Type} (spec : OracleSpec.{u} ι) : Type u → Type (u + 1)
  | pure' (α : Type u) (x : α) : OracleComp spec α
  | queryBind' (i : ι) (t : spec.domain i) (α : Type u)
      (ou : spec.range i → OracleComp spec α) : OracleComp spec α
  | failure' (α : Type u) : OracleComp spec α

abbrev ProbComp := OracleComp unifSpec

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι}

instance {α : Type u} : Inhabited (OracleComp spec α) := ⟨failure' α⟩

/-- Returns `true` for computations that don't query any oracles or fail, else `false` -/
def isPure {α : Type u} : OracleComp spec α → Bool | pure' _ _ => true | _ => false

/-- Returns `true` for computations that fail else `false`. -/
def isFailure {α : Type u} : OracleComp spec α → Bool | failure' _ => true | _ => false

section Monad

variable {α β : Type u}

/-- Bind operator on `OracleComp spec` operation used in the monad definition. -/
def bind' : (α β : Type u) → OracleComp spec α → (α → OracleComp spec β) → OracleComp spec β
  | _, _, pure' _ a, ob => ob a
  | α, β, queryBind' i t _ oa, ob => queryBind' i t β (λ u ↦ bind' α β (oa u) ob)
  | _, β, failure' _, _ => failure' β

/-- `OracleComp spec` forms a monad under `OracleComp.pure'` and `OracleComp.bind'`. -/
instance : Monad (OracleComp spec) where
  pure x := pure' _ x
  bind oa ob := bind' _ _ oa ob

/-- `OracleComp spec` has the obvious `Alternative` instance, where failure is `failure'`. -/
instance : Alternative (OracleComp spec) where
  failure {α} := failure' α
  orElse oa₁ oa₂ := if oa₁.isFailure then oa₂ () else oa₁

@[simp] protected lemma pure'_eq_pure (spec : OracleSpec ι) (a : α) :
  pure' α a = (pure a : OracleComp spec α) := rfl
@[simp] protected lemma bind'_eq_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
  bind' α β oa ob = oa >>= ob := rfl
@[simp] protected lemma failure'_eq_failure (spec : OracleSpec ι) (α : Type) :
  failure' α = (failure : OracleComp spec α) := rfl

instance (spec : OracleSpec ι) : LawfulMonad (OracleComp spec) :=
  LawfulMonad.mk' _
    (λ oa ↦ by
      induction' oa with α a i t α oa hoa α; rfl
      exact congr_arg (queryBind' i t α) (funext (λ u ↦ hoa u)); rfl)
    (λ x ob ↦ rfl)
    (λ oa ob oc ↦ by
      induction' oa with α a i t α oa hoa; rfl
      exact congr_arg (queryBind' i t _) <| funext (λ u ↦ hoa u ob); rfl)

@[simp] lemma failure_bind (ob : α → OracleComp spec β) : failure >>= ob = failure := rfl

@[simp] lemma map_failure (f : α → β) : f <$> (failure : OracleComp spec α) = failure := rfl

@[simp] lemma failure_seq (ob : OracleComp spec α) :
    (failure : OracleComp spec (α → β)) <*> ob = failure := rfl

protected lemma bind_congr {oa oa' : OracleComp spec α} {ob ob' : α → OracleComp spec β}
    (h : oa = oa') (h' : ∀ x, ob x = ob' x) : oa >>= ob = oa' >>= ob' :=
  h ▸ (congr_arg (λ ob ↦ oa >>= ob) (funext h'))

end Monad

section query

/-- `query i t` represents querying the oracle corresponding to `i` on input `t`.
The continuation for the computation in this case just returns the original result-/
def query {spec : OracleSpec ι} (i : ι) (t : spec.domain i) : OracleComp spec (spec.range i) :=
  queryBind' i t (spec.range i) pure

variable (i : ι) (t : spec.domain i)

lemma query_def : query i t = queryBind' i t (spec.range i) pure := rfl

@[simp] lemma queryBind'_eq_queryBind {α : Type} (oa : spec.range i → OracleComp spec α) :
    queryBind' i t α oa = query i t >>= oa := rfl

end query

section mapM

/-- Implement all queries in a computation using some other monad `m`,
preserving the pure and bind operations, giving a computation in the new monad. -/
protected def mapM {ι : Type} {spec : OracleSpec.{u} ι}
    {m : Type u → Type w} [Monad m] [Alternative m] :
    {α : Type u} → (oa : OracleComp spec α) →
      (f : (i : ι) → spec.domain i → m (spec.range i)) → m α
  | _, pure' α x, _ => return x
  | _, failure' _, _ => failure
  | _, queryBind' i t _ oa, f => (do let u ← f i t; OracleComp.mapM (oa u) f)

end mapM

/-- `coin` is the computation representing a coin flip, given a coin flipping oracle. -/
@[reducible, inline]
def coin : OracleComp coinSpec Bool := query () ()

/-- `$[0..n]` is the computation choosing a random value in the given range, inclusively.
By making this range inclusive we avoid the case of choosing from the empty range. -/
@[reducible, inline]
def uniformFin (n : ℕ) : ProbComp (Fin (n + 1)) := query n ()

notation "$[0.." n "]" => uniformFin n

example : ProbComp ℕ := do
  let x ← $[0..31415]; let y ← $[0..16180]
  return x + 2 * y

/-- Total number of queries in a computation across all possible execution paths.
Can be a helpful alternative to `sizeOf` when proving recursive calls terminate. -/
def totalQueries {α : Type u} : (oa : OracleComp spec α) → ℕ
  | queryBind' _ _ _ oa => 1 + ∑ u, totalQueries (oa u) | _ => 0

/-- Nicer induction rule for `OracleComp` that uses monad notation.
Allows inductive definitions on compuations by considering the three cases:
* `return x` / `pure x` for any `x`
* `do let u ← query i t; oa u` (with inductive results for `oa u`)
* `failure`
See `oracleComp_emptySpec_equiv` for an example of using this in a proof. -/
@[elab_as_elim]
protected def inductionOn {α : Type} {C : OracleComp spec α → Sort*}
    (pure : ∀ (a : α), C (pure a)) (query_bind : ∀ (i : ι) (t : spec.domain i)
      (oa : spec.range i → OracleComp spec α), (∀ u, C (oa u)) → C (do let u ← query i t; oa u))
    (failure : C failure) : (oa : OracleComp spec α) → C oa
  | pure' _ a => pure a
  | queryBind' i t _ oa => query_bind i t oa (λ u ↦
      have : totalQueries (oa u) < totalQueries (queryBind' i t α oa) :=
        Nat.lt_one_add_iff.2 <| Finset.single_le_sum (f := λ u ↦ totalQueries (oa u))
          (λ _ _ ↦ zero_le') (Finset.mem_univ u)
      OracleComp.inductionOn pure query_bind failure (oa u))
  | failure' _ => failure
  termination_by oa => totalQueries oa

@[elab_as_elim]
protected def induction {α : Type} {C : OracleComp spec α → Sort*} (oa : OracleComp spec α)
    (pure : ∀ (a : α), C (pure a)) (query_bind : ∀ (i : ι) (t : spec.domain i)
      (oa : spec.range i → OracleComp spec α), (∀ u, C (oa u)) → C (do let u ← query i t; oa u))
    (failure : C failure) : C oa := oa.inductionOn pure query_bind failure

variable {α β : Type}

section noConfusion

variable (i : ι) (t : spec.domain i) (u : spec.range i) (x : α)
  (ou : spec.range i → OracleComp spec α)
  (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β)

@[simp] lemma isPure_pure : isPure (pure x : OracleComp spec α) = true := rfl
@[simp] lemma isPure_query_bind : isPure (query i t >>= ou) = false := rfl
@[simp] lemma isPure_failure : isPure (failure : OracleComp spec α) = false := rfl
@[simp] lemma isFailure_pure (spec : OracleSpec ι) (x : α) :
    isFailure (pure x : OracleComp spec α) = false := rfl
@[simp] lemma isFailure_query_bind (i : ι) (t : spec.domain i)
    (oa : spec.range i → OracleComp spec β) : isFailure (query i t >>= oa) = false := rfl
@[simp] lemma isFailure_failure : isFailure (failure : OracleComp spec α) = true := rfl

@[simp] lemma pure_ne_query : pure u ≠ query i t := OracleComp.noConfusion
@[simp] lemma query_ne_pure : query i t ≠ pure u := OracleComp.noConfusion
@[simp] lemma pure_ne_query_bind : pure x ≠ query i t >>= ou := OracleComp.noConfusion
@[simp] lemma query_bind_ne_pure : query i t >>= ou ≠ pure x := OracleComp.noConfusion
@[simp] lemma pure_ne_failure : (pure x : OracleComp spec α) ≠ failure := OracleComp.noConfusion
@[simp] lemma failure_ne_pure : failure ≠ (pure x : OracleComp spec α) := OracleComp.noConfusion
@[simp] lemma query_ne_failure : query i t ≠ failure := OracleComp.noConfusion
@[simp] lemma failure_ne_query : failure ≠ query i t := OracleComp.noConfusion
@[simp] lemma failure_ne_query_bind : failure ≠ query i t >>= ou := OracleComp.noConfusion
@[simp] lemma query_bind_ne_failure : query i t >>= ou ≠ failure := OracleComp.noConfusion

lemma exists_eq_of_isPure {oa : OracleComp spec α} (h : isPure oa) :  ∃ x, oa = pure x := by
  induction oa using OracleComp.inductionOn with
  | pure => apply exists_apply_eq_apply' | query_bind => simp at h | failure => simp at h
lemma eq_failure_of_isFailure {oa : OracleComp spec α} (h : isFailure oa) : oa = failure := by
  induction oa using OracleComp.inductionOn with
  | pure => simp at h | query_bind => simp at h | failure => rfl

end noConfusion

section inj

@[simp] lemma pure_inj (x y : α) : (pure x : OracleComp spec α) = pure y ↔ x = y :=
  ⟨λ h ↦ OracleComp.noConfusion h (λ _ hx ↦ eq_of_heq hx), λ h ↦ h ▸ rfl⟩

@[simp] lemma query_inj (i : ι) (t t' : spec.domain i) : query i t = query i t' ↔ t = t' :=
  ⟨λ h ↦ OracleComp.noConfusion h (λ _ ht _ _ ↦ eq_of_heq ht), λ h ↦ h ▸ rfl⟩

@[simp]
lemma queryBind_inj' (i i' : ι) (t : spec.domain i) (t' : spec.domain i')
    (oa : spec.range i → OracleComp spec α) (oa' : spec.range i' → OracleComp spec α) :
    query i t >>= oa = query i' t' >>= oa' ↔ ∃ h : i = i', h ▸ t = t' ∧ h ▸ oa = oa' := by
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · rw [← queryBind'_eq_queryBind, ← queryBind'_eq_queryBind] at h
    refine OracleComp.noConfusion h ?_
    rintro rfl ⟨rfl⟩ _ ⟨rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨rfl, rfl, rfl⟩ := h; rfl

lemma queryBind_inj (i : ι) (t t' : spec.domain i) (oa oa' : spec.range i → OracleComp spec α) :
    query i t >>= oa = query i t' >>= oa' ↔ t = t' ∧ oa = oa' :=
  by simp only [queryBind_inj', exists_const]

/-- If the final output type of a computation has decidable equality,
then computations themselves have decidable equality.
Note: This depends on the decidable instances in the oracle spec itself. -/
protected instance instDecidableEq [DecidableEq ι] [h : DecidableEq α] :
    DecidableEq (OracleComp spec α)
  | pure' _ x, pure' _ x' => by simpa [pure_inj x x'] using h x x'
  | pure' _ _, queryBind' _ _ _ _ => by simpa using instDecidableFalse
  | queryBind' _ _ _ _, pure' _ x => by simpa using instDecidableFalse
  | failure' _, failure' _ => by simpa using instDecidableTrue
  | failure' _, pure' _ _ => by simpa using instDecidableFalse
  | pure' _ _, failure' _ => by simpa using instDecidableFalse
  | failure' _, queryBind' _ _ _ _ => by simpa using instDecidableFalse
  | queryBind' _ _ _ _, failure' _ => by simpa using instDecidableFalse
  | queryBind' i t _ oa, queryBind' i' t' _ oa' => by
    by_cases hi : i = i'
    · induction hi; simp
      suffices Decidable (oa = oa') from inferInstance
      suffices Decidable (∀ u, oa u = oa' u) from decidable_of_iff' _ funext_iff
      suffices ∀ u, Decidable (oa u = oa' u) from Fintype.decidableForallFintype
      exact λ u ↦ OracleComp.instDecidableEq (oa u) (oa' u)
    · simpa [hi] using instDecidableFalse

end inj

@[simp]
lemma bind_eq_pure_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β) :
    oa >>= ob = pure y ↔ ∃ x : α, oa = pure x ∧ ob x = pure y := by
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · match oa with
    | pure' _ x => exact ⟨x, rfl, h⟩
    | queryBind' i t _ oa => simp at h
    | failure' _ => simp at h
  · obtain ⟨x, hxa, hxb⟩ := h
    rw [hxa, pure_bind, hxb]

@[simp]
lemma pure_eq_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β) :
    pure y = oa >>= ob ↔ ∃ x : α, oa = pure x ∧ ob x = pure y :=
  eq_comm.trans (bind_eq_pure_iff oa ob y)

alias ⟨_, bind_eq_pure⟩ := bind_eq_pure_iff
alias ⟨_, pure_eq_bind⟩ := pure_eq_bind_iff

/-- Given a computation `oa : OracleComp spec α`, construct a value `x : α`,
by assuming each query returns the `default` value given by the `Inhabited` instance.
Returns `none` if the default path would lead to failure.

TODO: `default_result` -/
def defaultResult {ι : Type} {spec : OracleSpec ι} {α : Type}
    (oa : OracleComp spec α) : Option α :=
  oa.induction some (λ _ _ _ dr ↦ dr default) none

/-- Computations without access to any oracles are equivalent to values of the return type.
`toFun` is slightly different than `defaultResult` in that it doesn't recurse at all. -/
def oracleComp_emptySpec_equiv (α : Type) : OracleComp []ₒ α ≃ Option α where
  toFun oa := match oa with
    | pure' _ x => some x
    | queryBind' i _ _ _ => Empty.elim i
    | failure' _ => none
  invFun x := match x with | some x => pure x | none => failure
  left_inv oa := by induction oa using OracleComp.induction with
    | pure x => rfl
    | query_bind i t oa hoa => exact Empty.elim i
    | failure => rfl
  right_inv x := match x with | some x => rfl | none => rfl

-- NOTE: This should maybe be a `@[simp]` lemma? `apply_ite` can't be a simp lemma in general.
lemma ite_bind (p : Prop) [Decidable p] (oa oa' : OracleComp spec α)
    (ob : α → OracleComp spec β) : ite p oa oa' >>= ob = ite p (oa >>= ob) (oa' >>= ob) :=
  apply_ite (· >>= ob) p oa oa'

end OracleComp
