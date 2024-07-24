/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.OracleSpec

/-!
# Computations with Oracle Access

A value `oa : OracleComp spec α` represents a computation with return type `α`,
with access to any of the oracles specified by `spec : OracleSpec`.
Returning a value `x` corresponds to the computation `pure' α x`.
The computation `queryBind' i t α oa` represents querying the oracle corresponding to index `i`
on input `t`, getting a result `u : spec.range i`, and then running `oa u`.

`pure' α a` gives a monadic `pure` operation, while a more general `>>=` operator
is derived by induction on the first computation (see `OracleComp.bind`).
This importantly allows us to define a `LawfulMonad` instance on `OracleComp spec`,
which isn't possible if a general bind operator is included in the main syntax.

We also define simple operations like `coin : OracleComp coinSpec Bool` for flipping a fair coin,
and `$[0..n] : OracleComp unifSpec (Fin (n + 1))` for selecting from an inclusive range.

Note that the monadic structure on `OracleComp` exists only for a fixed `OracleSpec`,
so it isn't possible to combine computations where one has a superset of oracles of the other.
We later introduce a set of type coercions that mitigate this for most common cases,
such as calling a computation with `spec` as part of a computation with `spec ++ spec'`.
-/

/-- `OracleComp spec α` represents computations with oracle access to oracles in `spec`,
where the final return value has type `α`.

The constructor `pure' α x` allow for returning a pure Lean value `x`,
and `queryBind' i t α oa` allows for querying oracle `i` on input `t`,
calling `oa` on the result of the oracle call.
We recursively define a more general monadic bind operation later. -/
inductive OracleComp {ι : Type} (spec : OracleSpec ι) : Type → Type 1
  | pure' (α : Type) (x : α) : OracleComp spec α
  | queryBind' (i : ι) (t : spec.domain i) (α : Type)
      (oa : spec.range i → OracleComp spec α) : OracleComp spec α

namespace OracleComp

/-- Given a computation `oa : OracleComp spec α`, construct a value `x : α`,
by assuming each query returns the `default` value given by the `Inhabited` instance. -/
def defaultResult {ι : Type} {spec : OracleSpec ι} : {α : Type} → OracleComp spec α → α
  | _, pure' α x => x
  | _, queryBind' _ _ α oa => defaultResult (oa default)

instance {ι : Type} (spec : OracleSpec ι) (α : Type) [h : Nonempty α] :
  Nonempty (OracleComp spec α) := h.elim (λ x ↦ ⟨pure' α x⟩)
instance {ι : Type} (spec : OracleSpec ι) (α : Type) [Inhabited α] :
  Inhabited (OracleComp spec α) := ⟨pure' α default⟩
instance {ι : Type} (spec : OracleSpec ι) (α : Type) [h : IsEmpty α] :
  IsEmpty (OracleComp spec α) := ⟨λ oa ↦ h.1 (defaultResult oa)⟩

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-- Extract an `Inhabited` instance on the output type of a computation. -/
def baseInhabited (oa : OracleComp spec α) : Inhabited α := ⟨oa.defaultResult⟩

section Monad

/-- Bind operator on `OracleComp spec` operation used in the monad definition. -/
def bind' : (α β : Type) → OracleComp spec α → (α → OracleComp spec β) → OracleComp spec β
  | _, _, pure' α a, ob => ob a
  | _, β, queryBind' i t α oa, ob => queryBind' i t β (λ u ↦ bind' α β (oa u) ob)

/-- `OracleComp spec` forms a monad under `OracleComp.pure'` and `OracleComp.bind'`. -/
instance {ι : Type} (spec : OracleSpec ι) : Monad (OracleComp spec) where
  pure := @pure' ι spec
  bind := @bind' ι spec

@[simp] protected lemma pure'_eq_pure (spec : OracleSpec ι) (a : α) :
  pure' α a = (pure a : OracleComp spec α) := rfl

@[simp] protected lemma bind'_eq_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
  bind' α β oa ob = oa >>= ob := rfl

instance (spec : OracleSpec ι) : LawfulMonad (OracleComp spec) :=
  LawfulMonad.mk' _
    (λ oa ↦ by
      induction' oa with α a i t α oa hoa; · rfl
      · exact congr_arg (queryBind' i t α) (funext (λ u ↦ hoa u)))
    (λ x ob ↦ rfl)
    (λ oa ob oc ↦ by
      induction' oa with α a i t α oa hoa; · rfl
      · exact congr_arg (queryBind' i t _) <| funext (λ u ↦ hoa u ob))

protected lemma bind_congr {oa oa' : OracleComp spec α} {ob ob' : α → OracleComp spec β}
    (h : oa = oa') (h' : ∀ x, ob x = ob' x) : oa >>= ob = oa' >>= ob' :=
  h ▸ (congr_arg (λ ob ↦ oa >>= ob) (funext h'))

-- This should maybe be a `@[simp]` lemma? `apply_ite` can't be a simp lemma in general.
lemma ite_bind (p : Prop) [Decidable p] (oa oa' : OracleComp spec α)
    (ob : α → OracleComp spec β) : ite p oa oa' >>= ob = ite p (oa >>= ob) (oa' >>= ob) :=
  apply_ite (· >>= ob) p oa oa'

end Monad

section query

/-- `query i t` represents querying the oracle corresponding to `i` on input `t`.
The continuation for the computation in this case just returns the original result-/
def query {spec : OracleSpec ι} (i : ι) (t : spec.domain i) : OracleComp spec (spec.range i) :=
  queryBind' i t (spec.range i) pure

variable (i : ι) (t : spec.domain i)

lemma query_def : query i t = queryBind' i t (spec.range i) pure := rfl

@[simp] lemma queryBind'_eq_queryBind (oa : spec.range i → OracleComp spec α) :
    queryBind' i t α oa = query i t >>= oa := rfl

end query

/-- `coin` is the computation representing a coin flip, given a coin flipping oracle. -/
@[reducible, inline]
def coin : OracleComp coinSpec Bool := query () ()

/-- `$[0..n]` is the computation choosing a random value in the given range, inclusively.
By making this range inclusive we avoid the case of choosing from the empty range.
note: could define `$[n..m]` instead as `(. + n) <$> $[0..(m - n)]`,
but there are issues when `m < n`. -/
@[reducible, inline]
def uniformFin (n : ℕ) : OracleComp unifSpec (Fin (n + 1)) := query n ()

notation "$[0.." n "]" => uniformFin n

example : OracleComp unifSpec ℕ := do
  let x ← $[0..31415]
  let y ← $[0..16180]
  return x + 2 * y

protected def inductionOn {ι : Type} {spec : OracleSpec ι}
    {C : Π {α : Type}, OracleComp spec α → Prop}
    (h_pure : ∀ {α : Type} (a : α), C (pure a))
    (h_queryBind : ∀ (i : ι) (t : spec.domain i) {α : Type}
      (oa : spec.range i → OracleComp spec α),
      (∀ u, C (oa u)) → C (query i t >>= oa)) :
    {α : Type} → (oa : OracleComp spec α) → C oa
  | _, (pure' α a) => h_pure a
  | _, (queryBind' i t α oa) => h_queryBind i t oa
    (λ u ↦ OracleComp.inductionOn h_pure h_queryBind (oa u))

/-- Computations without access to any oracles are equivalent to values of the return type. -/
def oracleComp_emptySpec_equiv (α : Type) : OracleComp []ₒ α ≃ α where
  toFun := λ oa ↦ match oa with
    | pure' α x => x
    | queryBind' i _ _ _ => Empty.elim i
  invFun := pure
  left_inv := λ oa ↦ match oa with
    | pure' α x => rfl
    | queryBind' i _ _ _ => Empty.elim i
  right_inv := λ _ ↦ rfl

section inj

@[simp] lemma pure_inj (x y : α) : (pure x : OracleComp spec α) = pure y ↔ x = y :=
  ⟨λ h ↦ OracleComp.noConfusion h (λ _ hx ↦ eq_of_heq hx), λ h ↦ h ▸ rfl⟩

@[simp] lemma query_inj (i : ι) (t t' : spec.domain i) : query i t = query i t' ↔ t = t' :=
  ⟨λ h ↦ OracleComp.noConfusion h (λ _ ht _ _ ↦ eq_of_heq ht), λ h ↦ h ▸ rfl⟩

@[simp]
lemma queryBind_inj (i i' : ι) (t : spec.domain i) (t' : spec.domain i')
    (oa : spec.range i → OracleComp spec α) (oa' : spec.range i' → OracleComp spec α) :
    query i t >>= oa = query i' t' >>= oa' ↔ ∃ h : i = i', h ▸ t = t' ∧ h ▸ oa = oa' := by
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · rw [← queryBind'_eq_queryBind, ← queryBind'_eq_queryBind] at h
    refine OracleComp.noConfusion h ?_
    rintro rfl ⟨rfl⟩ _ ⟨rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨rfl, rfl, rfl⟩ := h; rfl

end inj

section ne

variable (i : ι) (t : spec.domain i) (u : spec.range i) (x : α)
  (ou : spec.range i → OracleComp spec α)

@[simp] lemma pure_ne_query : pure u ≠ query i t := OracleComp.noConfusion
@[simp] lemma query_ne_pure : query i t ≠ pure u := OracleComp.noConfusion
@[simp] lemma pure_ne_queryBind : pure x ≠ query i t >>= ou := OracleComp.noConfusion
@[simp] lemma queryBind_ne_pure : query i t >>= ou ≠ (pure x) := OracleComp.noConfusion

end ne

section eq

variable (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β)

@[simp]
lemma bind_eq_pure_iff : oa >>= ob = pure y ↔ ∃ x : α, oa = pure x ∧ ob x = pure y := by
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · match oa with
    | pure' _ x => exact ⟨x, rfl, h⟩
    | queryBind' i t _ oa => simp at h
  · obtain ⟨x, hxa, hxb⟩ := h
    rw [hxa, pure_bind, hxb]

@[simp]
lemma pure_eq_bind_iff : pure y = oa >>= ob ↔ ∃ x : α, oa = pure x ∧ ob x = pure y :=
  eq_comm.trans (bind_eq_pure_iff oa ob y)

end eq

/-- If the final output type of a computation has decidable equality,
then computations themselves have decidable equality.
Note: This depends on the decidable instances in the oracle spec itself. -/
protected instance decidableEq [DecidableEq ι] [h : DecidableEq α] :
    DecidableEq (OracleComp spec α)
  | pure' _ x, pure' _ x' => by simpa [pure_inj x x'] using h x x'
  | pure' _ x, queryBind' i t _ oa => by simpa using Decidable.isFalse not_false
  | queryBind' i t _ oa, pure' _ x => by simpa using Decidable.isFalse not_false
  | queryBind' i t _ oa, queryBind' i' t' _ oa' => by
    by_cases hi : i = i'
    · induction hi; simp
      suffices Decidable (oa = oa') from inferInstance
      suffices Decidable (∀ u, oa u = oa' u) from decidable_of_iff' _ Function.funext_iff
      suffices ∀ u, Decidable (oa u = oa' u) from Fintype.decidableForallFintype
      exact λ u ↦ OracleComp.decidableEq (oa u) (oa' u)
    · simpa [hi] using Decidable.isFalse not_false

end OracleComp
