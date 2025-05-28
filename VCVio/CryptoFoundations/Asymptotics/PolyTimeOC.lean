/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Computability.TMComputable
import VCVio.OracleComp.OracleComp

/-!
# Polynomial Time Computations

Polynomial complexity for computations with oracles.

More background theory on `TM2ComputableInPolyTime` would be needed
to make this kind of approach usable in practice.

More adaptation would also be needed to handle dependent types
-/

open Computability Turing OracleSpec

variable {ι : Type _} {spec : OracleSpec ι}

/-- There exists encodings of types `α` and `β` into strings over a finite alphabet such
that the function `f : α → β` has a polynomial time implementation as a Turing machine.
This definition is just a wrapper around `TM2ComputableInPolyTime` that makes statements
propositional rather than carrying the TM implementation. -/
def IsComputableInPolyTime {α β : Type} (f : α → β) : Prop :=
  ∃ ea : Computability.FinEncoding α,
    ∃ eb : Computability.FinEncoding β,
      Nonempty (Turing.TM2ComputableInPolyTime ea eb f)

/-- Version of `TM2ComputableInPolyTime` for types that are parameterized by a security parameter,
with input/output types parameterized by some natural number. -/
structure IsPolyTimeInParam {α β : ℕ → Type}
    (f : (n : ℕ) → α n → β n) where
  time : Polynomial ℕ
  tm : ℕ → FinTM2
  ea (n : ℕ) : FinEncoding (α n)
  eb (n : ℕ) : FinEncoding (β n)
  inputAlphabet (n : ℕ) : (tm n).Γ (tm n).k₀ ≃ (ea n).Γ
  outputAlphabet (n : ℕ) : (tm n).Γ (tm n).k₁ ≃ (eb n).Γ
  outputsFun (n : ℕ) (inp : α n) :
    let encode_inp := List.map (inputAlphabet n).invFun ((ea n).encode inp)
    let encode_out := Option.some ((List.map (outputAlphabet n).invFun) ((eb n).encode (f n inp)))
    TM2OutputsInTime (tm n) encode_inp encode_out (time.eval n)

/-- Encode a finite type by using the type itself as the finite alphabet.
Values `x` can then be encoded as simply `[x]`. -/
def finEncodingFintypeSelf (α : Type _) [h : Fintype α] :
    Computability.FinEncoding α where
  Γ := α
  encode x := [x]
  decode xs := xs.head?
  decode_encode _ := List.head?_cons
  ΓFin := h

/-- The identity function over a finite time is polynomial time. -/
@[simp] lemma isComputableInPolyTime_id {α : Type} [Fintype α] :
    IsComputableInPolyTime (@id α) := by
  refine ⟨finEncodingFintypeSelf α, finEncodingFintypeSelf α, ⟨?_⟩⟩
  exact Turing.idComputableInPolyTime (finEncodingFintypeSelf α)

namespace OracleSpec

/-- `spec.FinEncodable` provides encodings of the oracle's domain and range types over
some (unspecified) finite alphabet. -/
class FinEncodable {ι : Type} (spec : OracleSpec ι) where
    domain_encoding (i : ι) : Computability.FinEncoding (spec.domain i)
    range_encoding (i : ι) : Computability.FinEncoding (spec.range i)

instance : unifSpec.FinEncodable where
  domain_encoding _ := finEncodingFintypeSelf Unit
  range_encoding n := finEncodingFintypeSelf (Fin (n + 1))

end OracleSpec

namespace OracleQuery

protected inductive PolyTime : {α β : Type} →
    (q : α → OracleQuery spec β) → Prop
  | polyTime_query {α : Type _} {i : ι} {t : α → spec.domain i}
      (h : IsComputableInPolyTime t) :
      OracleQuery.PolyTime (fun x => query i (t x))

def PolyTime_query_const (i : ι) [h : spec.FinEncodable] :
    OracleQuery.PolyTime (fun t : spec.domain i => query i t) :=
  OracleQuery.PolyTime.polyTime_query ⟨h.domain_encoding i, h.domain_encoding i,
    ⟨Turing.idComputableInPolyTime _⟩⟩

end OracleQuery

namespace OracleComp

protected inductive PolyTime {ι : Type _} {spec : OracleSpec ι} :
    {α β : Type _} → (α → OracleComp spec β) → Prop
  | polyTime_pure {α β : Type _} (f : α → β)
      (h : IsComputableInPolyTime f) :
      OracleComp.PolyTime (fun x => return (f x))
  | polyTime_query_bind {α β γ : Type _}
      (q : α → OracleQuery spec β)
      (ob : α → β → OracleComp spec γ)
      (h1 : OracleQuery.PolyTime q)
      (h2 : OracleComp.PolyTime (Function.uncurry ob)) :
      OracleComp.PolyTime (fun x => liftM (q x) >>= ob x)
  | polyTime_failure {α β : Type _} : OracleComp.PolyTime (fun _ => failure)
  | polyTime_compose {α β γ : Type _} (f : α → β) (oc : β → OracleComp spec γ)
      (h1 : IsComputableInPolyTime f)
      (h2 : OracleComp.PolyTime oc) :
      OracleComp.PolyTime (oc ∘ f)

end OracleComp
