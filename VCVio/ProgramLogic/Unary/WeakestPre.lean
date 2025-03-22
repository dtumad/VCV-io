import VCVio.OracleComp.OracleComp

/-!
  # Program Logic for `FreeMonad`

  We build a program logic for `FreeMonad` based on the paper
    [Program Logic a la Carte](https://dl.acm.org/doi/pdf/10.1145/3704847).

  While that paper uses `ITree`, it is essentially the same as `FreeMonad`, so adapting their work
  is straightforward.
-/

universe u v w

open OracleSpec

local instance {α} : Zero (Option α) where
  zero := none

/-- A heap of values of type `V` is a finite map from locations (indexed by `Nat`) to values of type `V`. -/
def Heap (V : Type u) := Finsupp Nat (Option V)

/-- Interaction trees. There are two main differences with `OracleComp`:

1. We have an extra constructor `tau` for a "do nothing" step (and we don't have `failure` option).

2. The visible event's continuation `t : α → ITree E α` takes

This definition of `ITree` is also different from the Coq version, in that it's **inductive** (e.g. least fix point) and not **co-inductive** (e.g. largest fix point). Hence we cannot reason about infinite `ITree`s, but this is also not a focus in our work. -/
inductive ITree (E : Type u → Type v) (α : Type u) where
  | pure (a : α)
  | tau (t : ITree E α)
  | vis (e : E α) (t : α → ITree E α)

-- Actually, `ITree` without `tau` is **exactly** `FreeMonad`!
#check FreeMonad
#print OracleSpec.OracleQuery


/-! ## Definitions of common events -/

namespace Event

/-- The empty event type, has no inductive constructors. -/
inductive Void : Type u → Type v

instance {α : Type u} : IsEmpty (Void α) where
  false := fun x => match x with | y => by contradiction

/-- The failure event for interaction trees, has a single event `fail : Fail α` -/
inductive Fail (α : Type u) : Type v where
  | fail

/-- The state event, parametrized by the state type `σ`, comes with two operations:

1. `get : State σ σ` to get the current state.
2. `put (s : σ) : State σ PUnit` to set the current state. -/
inductive State (σ : Type u) : Type u → Type u where
  | get : State σ σ
  | put (s : σ) : State σ PUnit

/-- The type of events for a heap of values of type `V`. -/
def HeapState (V : Type u) := State (Heap V)

/-- The event type for non-determinism, comes with a single event `choose` to non-deterministically
  choose an element of a given type. This will be handled / interpreted as either angelic (there
  exists a choice) or demonic (for all choices). -/
inductive NonDet : Type u → Type v where
  | choose (α : Type u) : NonDet α

/-- The sum of two event types. -/
def sum (E₁ : Type u → Type v) (E₂ : Type u → Type w) : Type u → Type (max v w) :=
  fun α => E₁ α ⊕ E₂ α

def sumEquivVoidLeft {E : Type u → Type v} {α : Type u} : sum Void E α ≃ E α where
  toFun := fun x => match x with | .inr y => y
  invFun := fun x => .inr x
  left_inv := by intro x; simp; split; rfl
  right_inv := by intro x; rfl

def sumEquivVoidRight {E : Type u → Type v} {α : Type u} : sum E Void α ≃ E α where
  toFun := fun x => match x with | .inl y => y
  invFun := fun x => .inl x
  left_inv := by intro x; simp; split; rfl
  right_inv := by intro x; rfl

@[inherit_doc] infixr:30 " ⊕ₑ " => sum

/-- The handler for a given event (needs to replace `Prop` with `iProp` once integrated with Iris).

Consists of a predicate on an event and a continuation condition, and the hypothesis that the
predicate is monotone.

Note on the monotone condition: when we integrate with Iris, we will need to replace `→` with `-*`,
and add `□` to the second hypothesis.
  -/
structure Handler (E : Type u → Type v) where
  toFun : {α : Type u} → E α → (α → Prop) → Prop
  is_mono {α : Type u} {Φ Φ' : α → Prop} (hΦ : ∀ a, Φ a → Φ' a) (e : E α) : toFun e Φ → toFun e Φ'

instance {E} : CoeFun (Handler E) (fun _ => {α : Type u} → E α → (α → Prop) → Prop) where
  coe := Handler.toFun

namespace Handler

variable {E₁ : Type u → Type v} {E₂ : Type u → Type w}

/-- The handler for the sum of two event types, given individual handlers for each event type. -/
def sum (H₁ : Handler E₁) (H₂ : Handler E₂) : Handler (E₁ ⊕ₑ E₂) where
  toFun := Sum.elim H₁.toFun H₂.toFun
  is_mono := fun hΦ e h => by
    match e with
    | .inl e => exact H₁.is_mono hΦ e h
    | .inr e => exact H₂.is_mono hΦ e h

/-- A handler is monotone if it respects the ordering on the continuation & spawning threads
    conditions.-/
class IsMono {E : Type u → Type v} (H : Handler E) where
  is_mono {α : Type u} {Φ Φ' : α → Prop} (hΦ : ∀ a, Φ a → Φ' a) (e : E α) : H e Φ → H e Φ'

instance {H₁ : Handler E₁} {H₂ : Handler E₂} [IsMono H₁] [IsMono H₂] : IsMono (sum H₁ H₂) where
  is_mono := fun hΦ e h => match e with
    | .inl e => IsMono.is_mono hΦ e h
    | .inr e => IsMono.is_mono hΦ e h

end Handler

/-- The handler for the failure event, which sends everything to `False`. -/
def handleFail : Handler Fail where
  toFun := fun e _ => False
  is_mono := fun hΦ e h => by simp [h]

/-- The handler for angelic non-determinism, which asserts that there exists some value that
  satisfies the continuation. -/
def handleNonDetAngelic : Handler NonDet where
  toFun := fun e Φ => match e with | .choose _ => ∃ a, Φ a
  is_mono := fun hΦ e h => match e with
    | .choose _ => let ⟨a, h⟩ := h; ⟨a, hΦ a h⟩

/-- The handler for demonic non-determinism, which asserts that all values must satisfy the
  continuation. -/
def handleNonDetDemonic : Handler NonDet where
  toFun := fun e Φ => match e with | .choose _ => ∀ a, Φ a
  is_mono := fun hΦ e h => match e with
    | .choose _ => by simp_all

-- def handleState {σ} : Handler (State σ) := fun e Φ => match e with
--   | .get => Φ (State.get)
--   | .put s => Φ (State.put s)

-- def handleHeap : Handler (HeapState V) := fun e Φ => match e with
--   | .get => Φ (HeapState.get)
--   | .put s => Φ (HeapState.put s)

end Event

open Event

namespace FreeMonad

#check FreeMonad.mapM

variable {E : Type u → Type v} {f : Type u → Type v} {m : Type u → Type w} [Pure m] [Bind m]

-- @[simp]
-- lemma bind_eq_pure_iff (x : FreeMonad f α) (r : α → FreeMonad f β) (b : β) :
--     FreeMonad.bind x r = FreeMonad.pure b ↔ ∃ a, x = FreeMonad.pure a ∧ r a = FreeMonad.pure b := by
--   induction x with
--   | pure a => simp [bind_pure]
--   | roll x r ih => simp [bind_roll]

theorem mapM_eq_freeMonad_pure_iff {s : {α : Type u} → f α → FreeMonad E α} {α : Type u} (oa : FreeMonad f α) (a : α) :
    FreeMonad.mapM s oa = FreeMonad.pure a ↔
      (oa = FreeMonad.pure a) ∨
        (∃ β x r b, oa = .roll (β := β) x r ∧ (s x) = .pure b ∧ (r b).mapM s = FreeMonad.pure a) := by
  induction oa with
  | pure x => simp [mapM, bind_eq_pure_iff]
  | @roll β x r ih =>
    simp [mapM, ih]
    constructor <;> intro h
    · refine ⟨β, x, r, ?_⟩
      simp [h]
      simp_all only [exists_and_left]
    · simp_all only [exists_and_left]
      obtain ⟨w, h⟩ := h
      obtain ⟨w_1, h⟩ := h
      obtain ⟨w_2, h⟩ := h
      obtain ⟨left, right⟩ := h
      obtain ⟨left, right_1⟩ := left
      obtain ⟨w_3, h⟩ := right
      obtain ⟨left_1, right⟩ := right_1
      obtain ⟨left_2, right_1⟩ := h
      subst left
      simp_all only [heq_eq_eq, pure.injEq, exists_eq_left']

instance : AlternativeMonad (FreeMonad (E ⊕ₑ Fail)) where
  failure := .roll (Sum.inr $ Fail.fail) .pure
  orElse := fun _ y => y ()

-- instance : LawfulAlternative (FreeMonad (E ⊕ₑ Fail)) where
--   failure_bind g := by simp only [bind, failure, bind_roll, bind_pure]; sorry
--   mapConst_failure {α β : Type u} (y : β) : Functor.mapConst y (failure : FreeMonad (E ⊕ₑ Fail) α) = failure := by simp [Functor.mapConst, failure]
--   orElse_failure {α : Type u} (x : FreeMonad (E ⊕ₑ Fail) α) : (x <|> failure) = x := sorry
--   failure_orElse {α : Type u} (y : FreeMonad (E ⊕ₑ Fail) α) : (failure <|> y) = y := sorry

def handleFailRight {α : Type u} : FreeMonad (E ⊕ₑ Fail) α → OptionT (FreeMonad E) α :=
  FreeMonad.mapM (fun a => match a with
    | .inl e => .roll e (fun b => .pure (some b))
    | .inr .fail => FreeMonad.pure none)

def sumFailEquivOptionT (E : Type u → Type v) {α : Type u} :
    FreeMonad (E ⊕ₑ Fail) α ≃ OptionT (FreeMonad E) α where
  toFun := handleFailRight
    -- | .pure a => sorry
    -- | .roll (.inr .fail) _ => sorry
    -- | .roll (.inl e) a => .roll e (fun b => failEquivOption E (a b))
  invFun := OptionT.mapM (FreeMonad.mapM (fun e => .roll (Sum.inl e) .pure))
  left_inv := by
    intro x; simp [handleFailRight, OptionT.mapM, OptionT.run, pure, bind, OptionT.bind, OptionT.pure, OptionT.mk];
    rcases x with x | x
    · simp [pure, OptionT.pure, OptionT.mk]
    · simp [failure, bind, OptionT.bind, OptionT.mk]
      unfold FreeMonad.bind
      split <;> simp_all <;> sorry
  right_inv := by
    intro x
    rcases x with x | x
    · simp [OptionT.mapM, OptionT.run]
      rcases x
      · simp [failure, handleFailRight]
      · rfl
    · simp [OptionT.mapM, OptionT.run, bind, OptionT.bind, OptionT.mk, handleFailRight]
      congr
      funext a
      simp [FreeMonad.bind, failure]
      sorry

variable {E : Type u → Type v} {α β : Type u}

/-- Weakest precondition of a `FreeMonad` program, with respect to a postcondition and a handler for
  the events.

  When we integrate with Iris, we will need to wrap the update modality `⇛` around this. -/
def wp (H : Handler E) (Φ : α → Prop) : FreeMonad E α → Prop
  | .pure a => Φ a
  | .roll e r => H e (fun a => wp H Φ (r a))

variable {H : Handler E} {Φ Φ' : α → Prop}

-- For the theorems below, we will replace `↔` with bi-implication `⊣⊢` once integrated with Iris.

/-- The weakest precondition of a pure program is equivalent to the postcondition applied to the
  result. -/
@[simp]
theorem wp_pure {a : α} : wp H Φ (FreeMonad.pure a) ↔ Φ a := by simp [wp]

/-- The weakest precondition of a `roll` is equivalent to the handler's condition applied to the
  weakest precondition of the continuation. -/
@[simp]
theorem wp_roll {e : E α} {r : α → FreeMonad E α} :
    wp H Φ (FreeMonad.roll e r) ↔ H e (fun a => wp H Φ (r a)) := by simp [wp]

/-- The weakest precondition of an event (lifted to `FreeMonad`) is equivalent to the handler's
  condition. -/
@[simp]
theorem wp_event {e : E α} : wp H Φ (FreeMonad.lift e) ↔ H e Φ := by simp [lift, wp]

/-- The weakest precondition of a `bind` is equivalent to sequencing the weakest precondition of the
  first program with the weakest precondition of the second program. -/
@[simp]
theorem wp_bind {x : FreeMonad E β} {f : β → FreeMonad E α} :
    wp H Φ (FreeMonad.bind x f) ↔ wp H (fun a => wp H Φ (f a)) x := by
  induction x with
  | pure a => simp [wp]
  | roll e r ih => simp [wp, ih]

/-- The consequence rule for weakest preconditions: if `Φ` entails `Φ'`, then `wp H Φ x` entails
  `wp H Φ' x`. -/
theorem wp_conseq {x : FreeMonad E α} (hΦ : ∀ a, Φ a → Φ' a) (h : wp H Φ x) : wp H Φ' x := by
  induction x with
  | pure a => exact hΦ a h
  | roll e r ih => exact H.is_mono ih e h

alias wp_mono := wp_conseq

/-- The frame rule for weakest preconditions: both `P` and `wp H Φ x` hold if and only if
  `wp H (fun a => P ∧ Φ a) x` holds. -/
theorem wp_frame {x : FreeMonad E α} {P : Prop} : P ∧ wp H Φ x ↔ wp H (fun a => P ∧ Φ a) x := by
  induction x with
  | pure a => simp_all
  | roll e r ih => simp_all [wp, ih]; sorry

/-- Hoare triple for `FreeMonad` programs, defined in terms of weakest preconditions. -/
def hoareTriple (H : Handler E) (Ψ : Prop) (Φ : α → Prop) (x : FreeMonad E α) : Prop :=
  -- Replace `→` with `-*` once integrated with Iris.
  Ψ → wp H Φ x

end FreeMonad

variable {ι : Type u} {spec : OracleSpec ι} {α : Type w}

def OracleComp.ofFreeMonadSumFail : FreeMonad (OracleQuery spec ⊕ₑ Fail) α → OracleComp spec α :=
  FreeMonad.handleFailRight
