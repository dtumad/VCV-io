import VCVio

open Mathlib OracleSpec OracleComp AsymmEncAlg

section vectorAdd
-- Define vector addition more generally

instance {α : Type} {n : ℕ} [Add α] : Add (Vector α n) where
  add v1 v2 := Vector.ofFn (v1.get + v2.get)

instance {α : Type} {n : ℕ} [Zero α] : Zero (Vector α n) where
  zero := Vector.ofFn (0)

-- theorem addInst

theorem vectorAdd_get {α : Type} {n : ℕ} [Add α] [Zero α] (vx : Vector α n) (vy : Vector α n) : (vx + vy).get = vx.get + vy.get := by
  ext i
  simp
  unfold HAdd.hAdd
  rw [instHAdd]; simp
  unfold Add.add
  simp_rw [instAddVector_examples]
  rw [Vector.get]; simp
  unfold HAdd.hAdd
  rfl

theorem vectorofFn_get {α : Type} {n : ℕ} (v : Fin n → α) : (Vector.ofFn v).get = v := by
  ext i
  apply Vector.getElem_ofFn

end vectorAdd

-- #check AtLeastTwo

def regevAsymmEnc (n m χ p : ℕ) (herr: p > 2*χ) (hp2 : p > 1) : AsymmEncAlg ProbComp
    (M := Bool) (PK := Matrix (Fin n) (Fin m) (Fin p) × Vector (Fin p) m) (SK := Vector (Fin p) n) (C := Vector (Fin p) n × Fin p) where
  keygen := do
    have : NeZero p := ⟨by omega⟩
    let A ←$ᵗ Matrix (Fin n) (Fin m) (Fin p)
    let s ←$ᵗ Vector (Fin p) n
    let e ←$ᵗ Vector (Fin (2*χ + 1)) m
    -- let err := e.map (fun t ↦ (Fin.castLE herr t) - χ)
    let ecast := e.map (Fin.castLE herr)
    let err := ecast.map (Fin.sub χ)
    return ((A, Vector.ofFn (Matrix.vecMul s.get A) + err), s)
  encrypt := λ (A, y) msg ↦ do
    have : NeZero p := ⟨by omega⟩
    let r2 ←$ᵗ Vector (Fin 2) m
    let r := (r2.map (Fin.castLE hp2)).get
    let yr := dotProduct y.get r
    let signal := if msg then 0 else p / 2
    return (Vector.ofFn (Matrix.mulVec A r), yr + signal)
  decrypt := λ s (a, b) ↦ do
    have : NeZero p := ⟨by omega⟩
    let sa := dotProduct s.get a.get
    let val := Fin.val (sa - b)
    return if val < p/4 then true else val > 3*p/4
  __ := ExecutionMethod.default

section useful_lemmas
-- Useful lemmas for the proof
def Fin_Bound {n : ℕ} (x : Fin n) (b : ℕ) : Prop :=
  x.val ≤ b ∨ x.val ≥ n - b

def Fin_Bound_vec {n m : ℕ} (v : Vector (Fin n) m) (b : ℕ) : Prop :=
  ∀ i, Fin_Bound (v.get i) b

lemma Fin_Bound_ge {n b₁ b₂ : ℕ} {x : Fin n} (h : Fin_Bound x b₁) (g : b₁ ≤ b₂) : Fin_Bound x b₂ := by
  cases h
  . left; omega
  . right; omega
end useful_lemmas

namespace Regev

variable (n m χ p : ℕ) (h: NeZero p) (herr: p > 2*χ) (hp2 : p > 1)

section sound

theorem isCorrect : (regevAsymmEnc n m χ p herr hp2).PerfectlyCorrect := by
  rintro msg
  simp [CorrectExp, regevAsymmEnc]
  rintro A s e r
  let rv := (Vector.map (Fin.castLE hp2) r).get
  have h1 : rv = (Vector.map (Fin.castLE hp2) r).get := rfl
  simp_rw [← h1, vectorofFn_get]
  have pne0 : NeZero p := ⟨by omega⟩
  cases msg <;> simp
  . constructor
    . nth_rw 2 [Matrix.dotProduct_comm]
      rw [vectorAdd_get, Matrix.dotProduct_add, vectorofFn_get]
      nth_rw 2 [Matrix.dotProduct_comm]
      rw [← Matrix.dotProduct_mulVec]
      rw [add_assoc, sub_add_cancel_left]
      sorry
    . sorry
  . sorry

end sound

end Regev
