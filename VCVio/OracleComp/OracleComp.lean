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
import VCVio.OracleComp.OracleQuery
import ToMathlib.PFunctor.Free

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

open OracleSpec

/-- `OracleComp spec α` represents computations with oracle access to oracles in `spec`,
where the final return value has type `α`.
The basic computation is just an `OracleQuery`, augmented with `pure` and `bind` by `FreeMonad`,
and `failure` is also added after by the `OptionT` transformer.

In practive computations in `OracleComp spec α` have have one of three forms:
* `return x` to succeed with some `x : α` as the result.
* `do u ← query i t; oa u` where `oa` is a continutation to run with the query result
See `OracleComp.inductionOn` for an explicit induction principle. -/
def OracleComp (spec : OracleSpec.{u,v}) : Type w → Type (max u v w) :=
  PFunctor.FreeM spec

/-- Simplified notation for computations with no oracles besides random inputs. -/
abbrev ProbComp : Type → Type := OracleComp unifSpec

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec} {α β : Type v}

instance (spec : OracleSpec) : Monad (OracleComp spec) :=
  inferInstanceAs (Monad spec.FreeM)
instance (spec : OracleSpec) : LawfulMonad (OracleComp spec) :=
  inferInstanceAs (LawfulMonad spec.FreeM)

instance [Inhabited α] : Inhabited (OracleComp spec α) := ⟨pure default⟩

section query

/-- query an oracle on in input `t` to get a result in the corresponding `range t`. -/
def query (t : spec.domain) : OracleComp spec (spec.range t) :=
  PFunctor.FreeM.lift ⟨t, id⟩

lemma query_def : query (spec := spec) = fun t => PFunctor.FreeM.lift ⟨t, id⟩ := rfl

/-- Version of `query_def` using a positive definition of lifting. -/
lemma query_def' : query (spec := spec) = fun t => PFunctor.FreeM.liftPos t := rfl

@[simp] lemma mapM_query {m} [Monad m] [LawfulMonad m]
    (f : (x : spec.domain) → m (spec.range x)) (t : spec.domain) :
    PFunctor.FreeM.mapM f (query t) = f t := by simp [query_def]

/-- `coin` is the computation representing a coin flip, given a coin flipping oracle. -/
@[reducible, inline] def coin : OracleComp coinSpec Bool :=
  query (spec := coinSpec) ()

lemma coin_def : coin = query () := rfl

/-- `$[0..n]` is the computation choosing a random value in the given range, inclusively.
By making this range inclusive we avoid the case of choosing from the empty range. -/
@[reducible, inline] def uniformFin (n : ℕ) : ProbComp (Fin (n + 1)) :=
  query (spec := unifSpec) n

notation "$[0.." n "]" => uniformFin n

lemma uniformFin_def (n : ℕ) : $[0..n] = query (spec := unifSpec) n := rfl

/-- Select uniformly from a non-empty range. The notation attempts to derive `h` automatically. -/
@[reducible, inline] def uniformRange (n m : ℕ) (h : n < m) :
    ProbComp (Fin (m + 1)) :=
  (fun ⟨x, hx⟩ => ⟨x + n, by omega⟩) <$> $[0..(m - n)]

/-- Tactic to attempt to prove `uniformRange` decreasing bound, similar to array indexing. -/
syntax "uniform_range_tactic" : tactic
macro "uniform_range_tactic" : tactic => `(tactic | trivial)
macro "uniform_range_tactic" : tactic => `(tactic | get_elem_tactic)

/-- Select uniformly from a range of numbers. Attempts to use `get-/
notation "$[" n "⋯" m "]" => uniformRange n m (by uniform_range_tactic)

lemma uniformRange_def (n m : ℕ) (h : n < m) : $[n⋯m] = uniformRange n m h := rfl

example {m n : ℕ} (h : m < n) : ProbComp ℕ := do
  let x ← $[314⋯31415]; let y ← $[0⋯10] -- Prove by trivial reduction
  let z ← $[m⋯n] -- Use value from hypothesis
  return x + 2 * y

end query

protected lemma pure_def (x : α) :
    (pure x : OracleComp spec α) = PFunctor.FreeM.pure x := rfl

protected lemma bind_def (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    oa >>= ob = PFunctor.FreeM.bind oa ob := rfl

protected lemma failure_def : (failure : OptionT (OracleComp spec) α) = OptionT.fail := rfl

protected lemma orElse_def (oa oa' : OptionT (OracleComp spec) α) : (oa <|> oa') = OptionT.mk
      (do match ← OptionT.run oa with | some a => pure (some a) | _  => OptionT.run oa') := rfl

protected lemma bind_congr' {oa oa' : OracleComp spec α} {ob ob' : α → OracleComp spec β}
    (h : oa = oa') (h' : ∀ x, ob x = ob' x) : oa >>= ob = oa' >>= ob' := h ▸ bind_congr h'

@[simp] -- NOTE: debatable if this should be simp
lemma guard_eq {spec : OracleSpec} (p : Prop) [Decidable p] :
    (guard p : OptionT (OracleComp spec) Unit) = if p then pure () else failure := rfl

-- NOTE: This should maybe be a `@[simp]` lemma? `apply_ite` can't be a simp lemma in general.
lemma ite_bind (p : Prop) [Decidable p] (oa oa' : OracleComp spec α)
    (ob : α → OracleComp spec β) : ite p oa oa' >>= ob = ite p (oa >>= ob) (oa' >>= ob) :=
  apply_ite (· >>= ob) p oa oa'

/-- Nicer induction rule for `OracleComp` that uses monad notation.
Allows inductive definitions on compuations by considering the three cases:
* `return x` / `pure x` for any `x`
* `do let u ← query i t; oa u` (with inductive results for `oa u`)
See `oracleComp_emptySpec_equiv` for an example of using this in a proof.
If the final result needs to be a `Type` and not a `Prop`, see `OracleComp.construct`. -/
@[elab_as_elim]
protected def inductionOn {C : OracleComp spec α → Prop}
    (pure : (a : α) → C (pure a))
    (query_bind : (t : spec.domain) →
      (oa : spec.range t → OracleComp spec α) → (∀ u, C (oa u)) → C (query t >>= oa))
    (oa : OracleComp spec α) : C oa :=
  PFunctor.FreeM.inductionOn pure query_bind oa

/-- Version of `OracleComp.inductionOn` that includes an `OptionT` in the monad stack
and requires an explicit case to handle `failure`. -/
@[elab_as_elim]
protected def inductionOnOptional {C : OptionT (OracleComp spec) α → Prop}
    (pure : (a : α) → C (pure a))
    (query_bind : (t : spec.domain) →
      (oa : spec.range t → OptionT (OracleComp spec) α) → (∀ u, C (oa u)) →
      C (query t >>= oa))
    (failure : C failure)
    (oa : OptionT (OracleComp spec) α) : C oa :=
  PFunctor.FreeM.inductionOn
    (fun | some x => pure x | none => failure)
    (fun t => query_bind t) oa

/-- Version of `OracleComp.inductionOn` with the computation at the start. -/
@[elab_as_elim]
protected def induction {C : OracleComp spec α → Prop}
    (oa : OracleComp spec α) (pure : (a : α) → C (pure a))
    (query_bind : (t : spec.domain) →
      (oa : spec.range t → OracleComp spec α) → (∀ u, C (oa u)) → C (query t >>= oa)) : C oa :=
  PFunctor.FreeM.inductionOn pure query_bind oa

/-- Version of `OracleComp.inductionOnOptional` with the computation at the start. -/
@[elab_as_elim]
protected def inductionOptional {C : OptionT (OracleComp spec) α → Prop}
    (oa : OptionT (OracleComp spec) α) (pure : (a : α) → C (pure a))
    (query_bind : (t : spec.domain) →
      (oa : spec.range t → OptionT (OracleComp spec) α) → (∀ u, C (oa u)) →
      C (query t >>= oa))
    (failure : C failure) : C oa :=
  PFunctor.FreeM.inductionOn
    (fun | some x => pure x | none => failure)
    query_bind oa

section construct

/-- Version of `construct` with automatic induction on the `query` in when defining the
`query_bind` case. Can be useful with `spec.DecidableEq` and `spec.FiniteRange`.
`mapM`/`simulateQ` is usually preferable to this if the object being constructed is a monad. -/
@[elab_as_elim]
protected def construct {C : OracleComp spec α → Type*}
    (pure : (a : α) → C (pure a))
    (query_bind : (t : spec.domain) →
      (oa : spec.range t → OracleComp spec α) →
      ((u : spec.range t) → C (oa u)) → C (query t >>= oa))
    (oa : OracleComp spec α) : C oa :=
  PFunctor.FreeM.construct pure query_bind oa

@[simp] lemma construct_pure (x : α)
    {C : OracleComp spec α → Type w} (h_pure : (a : α) → C (pure a))
    (h_query_bind : (t : spec.domain) →
        (oa : spec.range t → OracleComp spec α) →
        ((u : spec.range t) → C (oa u)) → C (query t >>= oa)) :
    OracleComp.construct h_pure h_query_bind (pure x) = h_pure x := rfl

@[simp] lemma construct_query (t : spec.domain)
    {C : OracleComp spec (spec.range t) → Type*} (h_pure : (u : spec.range t) → C (pure u))
    (h_query_bind : (t' : spec.domain) →
      (oa : spec.range t' → OracleComp spec (spec.range t)) →
      ((u : spec.range t') → C (oa u)) → C (query t' >>= oa)) :
    (OracleComp.construct h_pure h_query_bind (query t) : C (query t)) =
      h_query_bind t pure h_pure := rfl

@[simp] lemma construct_query_bind (t : spec.domain) (mx : spec.range t → OracleComp spec α)
    {C : OracleComp spec α → Type w} (h_pure : (a : α) → C (pure a))
    (h_query_bind : (t : spec.domain) →
        (mx : spec.range t → OracleComp spec α) →
        ((u : spec.range t) → C (mx u)) → C (query t >>= mx)) :
    OracleComp.construct h_pure h_query_bind (query t >>= mx) =
      h_query_bind t mx fun u => OracleComp.construct h_pure h_query_bind (mx u) := rfl

end construct

section noConfusion

variable (x : α) (y : β) (t : spec.domain) (u : spec.range t)
  (oa : β → OracleComp spec α) (ou : spec.range t → OracleComp spec α)

/-- Returns `true` for computations that don't query any oracles or fail, else `false`. -/
def isPure {α : Type v} : OracleComp spec α → Bool
  | PFunctor.FreeM.pure _ => true
  | PFunctor.FreeM.roll _ _ => false

@[simp] lemma isPure_pure : isPure (pure x : OracleComp spec α) = true := rfl
@[simp] lemma isPure_query : isPure (query t) = false := rfl
@[simp] lemma isPure_query_bind : isPure (query t >>= ou) = false := rfl

@[simp] lemma pure_ne_query : pure u ≠ query t := fun h => by simpa using congr_arg isPure h
@[simp] lemma query_ne_pure : query t ≠ pure u := fun h => by simpa using congr_arg isPure h

@[simp] lemma pure_ne_query_bind : pure x ≠ query t >>= ou := fun h => by
  simpa only [isPure_pure, isPure_query_bind, Bool.true_eq_false] using congr_arg isPure h
@[simp] lemma query_bind_ne_pure : query t >>= ou ≠ pure x := fun h => by
  simpa only [isPure_pure, isPure_query_bind, Bool.false_eq_true] using congr_arg isPure h

lemma pure_eq_query_iff_false : pure u = query t ↔ False := by simp
lemma query_eq_pure_iff_false : query t = pure u ↔ False := by simp

end noConfusion

/-- Given a computation `oa : OracleComp spec α`, construct a value `x : α`,
by assuming each query returns the `default` value given by the `Inhabited` instance.
Returns `none` if the default path would lead to failure. -/
def defaultResult [spec.Inhabited] (oa : OracleComp spec α) : Option α :=
  PFunctor.FreeM.mapM (fun _ => default) oa

/-- Total number of queries in a computation across all possible execution paths.
Can be a helpful alternative to `sizeOf` when proving recursive calls terminate. -/
def totalQueries [spec.Fintype] [spec.Inhabited] {α : Type v} (oa : OracleComp spec α) : ℕ := by
  induction oa using OracleComp.construct with
  | pure x => exact 0
  | query_bind t oa rec_n => exact 1 + ∑ x, rec_n x

section inj

/-- Two `pure` computations are equal iff they return the same value. -/
@[simp] lemma pure_inj (x y : α) : pure (f := OracleComp spec) x = pure y ↔ x = y :=
  PFunctor.FreeM.pure_inj x y

/-- Doing something with a query result is equal iff they query the same oracle
and perform identical computations on the output. -/
@[simp] lemma queryBind_inj (t t' : spec.domain) (ob : spec.range t → OracleComp spec β)
    (ob' : spec.range t' → OracleComp spec β) :
    (query t) >>= ob = (query t') >>= ob' ↔ ∃ h : t = t', h ▸ ob = ob' :=
  PFunctor.FreeM.roll_inj t t' ob ob'

/-- Binding two computations gives a pure operation iff the first computation is pure
and the second computation does something pure with the result. -/
@[simp] lemma bind_eq_pure_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β) :
    oa >>= ob = pure y ↔ ∃ x : α, oa = pure x ∧ ob x = pure y := by
  refine ⟨λ h ↦ ?_, λ h ↦ let ⟨x, ⟨h, h'⟩⟩ := h; h ▸ h'⟩
  simp [OracleComp.pure_def, PFunctor.FreeM.monad_bind_def] at h
  rw [PFunctor.FreeM.bind_eq_pure_iff] at h
  exact h

/-- Binding two computations gives a pure operation iff the first computation is pure
and the second computation does something pure with the result. -/
@[simp] lemma pure_eq_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β) :
    pure y = oa >>= ob ↔ ∃ x : α, oa = pure x ∧ ob x = pure y :=
  eq_comm.trans (bind_eq_pure_iff oa ob y)

alias ⟨_, bind_eq_pure⟩ := bind_eq_pure_iff
alias ⟨_, pure_eq_bind⟩ := pure_eq_bind_iff

end inj

-- /-- If the oracle indexing-type `ι`, output type `α`, and domains of all oracles have
-- `DecidableEq` then `OracleComp spec α` also has `DecidableEq`. -/
-- protected instance instDecidableEq [spec.Fintype] [hd : DecidableEq (spec.domain)]
--     [hι : DecidableEq ι] [h : DecidableEq α] : DecidableEq (OracleComp spec α) := fun
--   | _ => sorry
  -- | FreeMonad.pure (Option.some x), FreeMonad.pure (Option.some y) =>
  --   match h x y with
  --   | isTrue rfl => isTrue rfl
  --   | isFalse h => isFalse λ h' ↦ h (by rwa [FreeMonad.pure.injEq, Option.some_inj] at h')
  -- | FreeMonad.pure Option.none, FreeMonad.pure (Option.some y) => isFalse λ h ↦
  --     Option.some_ne_none y (by rwa [FreeMonad.pure.injEq, eq_comm] at h)
  -- | FreeMonad.pure (Option.some x), FreeMonad.pure Option.none => isFalse λ h ↦
  --     Option.some_ne_none x (by rwa [FreeMonad.pure.injEq] at h)
  -- | FreeMonad.pure Option.none, FreeMonad.pure Option.none => isTrue rfl
  -- | FreeMonad.pure x, FreeMonad.roll q r => isFalse <| by simp
  -- | FreeMonad.roll q r, FreeMonad.pure x => isFalse <| by simp
  -- | FreeMonad.roll (OracleQuery.query i t) r, FreeMonad.roll (OracleQuery.query i' t') s =>
  --   match hι i i' with
  --   | isTrue h => by
  --       induction h
  --    rw [FreeMonad.roll.injEq, heq_eq_eq, OracleQuery.query.injEq, eq_self, true_and, heq_eq_eq]
  --       refine @instDecidableAnd _ _ (hd i t t') ?_
  --       suffices Decidable (∀ u, r u = s u) from decidable_of_iff' _ funext_iff
  --       suffices ∀ u, Decidable (r u = s u) from Fintype.decidableForallFintype
  --       exact λ u ↦ OracleComp.instDecidableEq (r u) (s u)
  --   | isFalse h => isFalse λ h' ↦ h <|
  --       match FreeMonad.roll.inj h' with
  --       | ⟨h1, h2, _⟩ => @congr_heq _ _ ι OracleQuery.index OracleQuery.index
  --           (query i t) (query i' t') (h1 ▸ HEq.rfl) h2

end OracleComp
