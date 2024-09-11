/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio

/-!
# Random-Function Random-Permutation Switching Lemma
-/

open OracleSpec OracleComp

/-- Security adversary for RF-RP distinguisher experiments.
Has a single -/
def RF_RP_Adv (α : ℕ → Type) [∀ n, Fintype (α n)]
    [∀ n, Inhabited (α n)] [∀ n, DecidableEq (α n)] :=
  SecAdv (λ n ↦ unifSpec ++ₒ (α n →ₒ α n)) (λ _ ↦ Unit) (λ _ ↦ Bool)

variable {α : ℕ → Type} [∀ n, Fintype (α n)]
    [∀ n, Inhabited (α n)] [∀ n, DecidableEq (α n)]
    [∀ n, SelectableType (α n)]

def RF_Exp (adv : RF_RP_Adv α) :
    SecExp (λ n ↦ (α n →ₒ α n)) where
  main n := adv.run n ()
  baseState n := QueryCache (α n →ₒ α n)
  init_state _ := ∅
  baseSimOracle _ := randOracle

noncomputable def RP_Exp (adv : RF_RP_Adv α) :
    SecExp (λ n ↦ (α n →ₒ α n)) where
  main n := adv.run n ()
  baseState n := QueryCache (α n →ₒ α n) × Finset (α n)
  init_state _ := (∅, ∅)
  baseSimOracle _ := λ () t (cache, used) ↦ do
    let (u, cache') ← cache.lookup_or_else () t ($ usedᶜ)
    return (u, cache', insert u used)

instance  {ι ι' τ : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {source_spec : OracleSpec τ} {σ : Type}
    [∀ α, Coe (OracleComp spec α) (OracleComp spec' α)] :
    Coe (source_spec →[σ]ₛₒ spec) (source_spec →[σ]ₛₒ spec') where
  coe := λ so i t s ↦ ↑(so i t s)

section parallelAppend

def parallelAppend {ι₁ ι₂ ι₃ ι₄ : Type}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {spec₃ : OracleSpec ι₃} {spec₄ : OracleSpec ι₄} {σ τ : Type}
    (so : spec₁ →[σ]ₛₒ spec₂) (so' : spec₃ →[τ]ₛₒ spec₄) :
    spec₁ ++ₒ spec₃ →[σ × τ]ₛₒ spec₂ ++ₒ spec₄ :=
  ↑so ++ₛₒ ↑so'

infixl : 65 " ||ₛₒ " => parallelAppend

end parallelAppend


-- TODO: The inference rules with parallel append and interactions needing this
def simulate'' {ι ιₜ : Type} {spec : OracleSpec ι} {specₜ : OracleSpec ιₜ}
    {α σ : Type} (oa : OracleComp spec α) (so : spec →[σ]ₛₒ specₜ) (s : σ) :
  OracleComp specₜ α :=
  Prod.fst <$> simulate so s oa

example {α : Type} (oa : OracleComp unifSpec α) :
    OracleComp (unifSpec ++ₒ emptySpec) α := ↑oa

example (so : unifSpec →[Unit]ₛₒ unifSpec) :
    unifSpec →[Unit]ₛₒ unifSpec ++ₒ []ₒ := ↑so

-- Old version manually
noncomputable def RF_RP_Exp (adv : RF_RP_Adv α) [∀ n, SelectableType (α n → α n)]
    [∀ n, SelectableType {f : α n → α n // f.Bijective}] : SecExp (λ _ ↦ []ₒ) where
  main n := do
    let f ←$ᵗ (α n → α n) -- random function
    let g : {f : α n → α n // f.Bijective} ←$ᵗ {f : α n → α n // f.Bijective} -- random perm
    let b : Bool ←$ᵗ Bool
    let h : α n → α n := if b then f else g.1
    let so : (α n →ₒ α n) →[Unit]ₛₒ []ₒ :=
      λ _ t () ↦ return (h t, ())
    simulate' (idOracle ||ₛₒ so) ((), ()) (adv.run n ())
  __ := OracleAlg.baseOracleAlg
