import VCVio
import Mathlib.Tactic.Common

open Mathlib OracleSpec OracleComp AsymmEncAlg

section vectorAdd
-- Define vector addition more generally

instance {α : Type} {n : ℕ} [Add α] : Add (Vector α n) where
  add v1 v2 := Vector.ofFn (v1.get + v2.get)

instance {α : Type} {n : ℕ} [Zero α] : Zero (Vector α n) where
  zero := Vector.ofFn (0)

-- theorem addInst

@[simp]
theorem vectorofFn_get {α : Type} {n : ℕ} (v : Fin n → α) : (Vector.ofFn v).get = v := by
  ext i
  apply Vector.getElem_ofFn

@[simp]
theorem vectorAdd_get {α : Type} {n : ℕ} [Add α] [Zero α]
 (vx : Vector α n) (vy : Vector α n)
 : (vx + vy).get = vx.get + vy.get := by
  show (Vector.ofFn (vx.get + vy.get)).get = vx.get + vy.get
  simp

end vectorAdd

-- #check AtLeastTwo

def regevAsymmEnc (n m χ p : ℕ) (herr: p > 2*χ) (hp2 : p > 1) : AsymmEncAlg ProbComp
    (M := Bool) (PK := Matrix (Fin n) (Fin m) (Fin p) × Vector (Fin p) m) (SK := Vector (Fin p) n) (C := Vector (Fin p) n × Fin p) where
  keygen := do
    have : NeZero p := ⟨by omega⟩
    let A ←$ᵗ Matrix (Fin n) (Fin m) (Fin p)
    let s ←$ᵗ Vector (Fin p) n
    let e ←$ᵗ Vector (Fin (2*χ + 1)) m
    let err := e.map (fun t ↦ (Fin.castLE herr t) - χ)
    -- let ecast := e.map (Fin.castLE herr)
    -- let err := ecast.map (Fin.sub χ)
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
  x.val ≤ b ∨ x.val + b ≥ n

def Fin_Bound_vec {n m : ℕ} (v : Vector (Fin n) m) (b : ℕ) : Prop :=
  ∀ i, Fin_Bound (v.get i) b

@[simp]
lemma Fin_Bound_modulus {n : ℕ} (x : Fin n) : Fin_Bound x n := by
  left; simp

@[simp]
lemma Fin_Bound_ge {n b₁ b₂ : ℕ} {x : Fin n} (h : Fin_Bound x b₁)
 (g : b₁ ≤ b₂) : Fin_Bound x b₂ := by
  cases h
  . left; omega
  . right; omega

@[simp]
lemma Fin_bound_zero {n : ℕ} (x : Fin n) : Fin_Bound x 0 ↔ x.val = 0:= by
  constructor <;> intro h
  . rcases h with h | h
    . omega
    . simp at h
      have : x.val < n := by apply Fin.val_lt_of_le x (le_refl n)
      linarith
  . left
    linarith

@[simp]
lemma Fin_Bound_add {n b₁ b₂ : ℕ} {x y : Fin n} (h₁ : Fin_Bound x b₁)
 (h₂ : Fin_Bound y b₂) : Fin_Bound (x + y) (b₁ + b₂) := by
  rcases h₁ with h₁ | h₁
  . rcases h₂ with h₂ | h₂
    . left
      rw [Fin.val_add_eq_ite]
      by_cases h : n ≤ x.val + y.val <;> simp [h] <;> linarith
    . by_cases h : n ≤ x.val + y.val
      . left
        simp [Fin.val_add_eq_ite, h]
        have := Fin.val_lt_of_le y (le_refl n)
        omega
      . right
        simp [Fin.val_add_eq_ite, h]
        omega
  . rcases h₂ with h₂ | h₂
    . by_cases h : n ≤ x.val + y.val
      . left
        simp [Fin.val_add_eq_ite, h]
        have := Fin.val_lt_of_le x (le_refl n)
        omega
      . right
        simp [Fin.val_add_eq_ite, h]
        omega
    . right
      rw [Fin.val_add_eq_ite]
      by_cases h : n ≤ x.val + y.val <;> simp [h] <;> omega

lemma Fin_bound_mul_helper {n b₁ b₂ : ℕ} {x y : Fin n} (h : b₁ * b₂ < n)
  (h₁ : x.val ≤ b₁) (h₂ : y.val + b₂ ≥ n) : Fin_Bound (x * y) (b₁ * b₂) := by
  by_cases g : x.val = 0
  . left; simp [Fin.val_mul, g]
  right
  rw [Fin.val_mul]
  have hy : y.val < n := by apply Fin.val_lt_of_le y (le_refl n)
  have hc : ∃ c ≤ b₂, y.val + c = n := by
    use n - y.val; constructor <;> omega
  rcases hc with ⟨c, hc1, hc2⟩
  have h3 : x.val * y.val + x.val * c = n * x.val := by
    rw [← mul_add, hc2]; apply mul_comm
  calc x.val * y.val % n + b₁ * b₂ ≥ x.val * y.val % n + b₁ * b₂ := by rfl
    _ ≥ x.val * y.val % n + b₁ * c := by
      apply Nat.mul_le_mul_left b₁ at hc1
      exact Nat.add_le_add_left hc1 (↑x * ↑y % n)
    _ ≥ x.val * y.val % n + x.val * c := by
      apply Nat.mul_le_mul_left c at h₁
      apply Nat.add_le_add_left
      linarith [h₁]
    _ ≥ x.val * y.val % n + x.val * c % n := by
      apply Nat.add_le_add_left
      exact Nat.mod_le (x.val * c) n
    _ ≥ n := by
      contrapose g; simp at g; simp
      apply Nat.add_mod_of_add_mod_lt at g
      rw [h3, Nat.mul_mod_right] at g
      symm at g
      rw [Nat.add_eq_zero] at g
      rcases g with ⟨g1, g2⟩
      have : x.val * c < n := by
        apply lt_of_le_of_lt _ h
        trans (b₁ * c)
        exact Nat.mul_le_mul_right c h₁
        exact Nat.mul_le_mul_left b₁ hc1
      apply Nat.mod_eq_of_lt at this
      have hcn0 : c ≠ 0 := by omega
      rw [g2] at this
      symm at this; apply mul_eq_zero.1 at this
      tauto

@[simp]
lemma Fin_Bound_mul {n b₁ b₂ : ℕ} {x y : Fin n} (h₁ : Fin_Bound x b₁)
 (h₂ : Fin_Bound y b₂) : Fin_Bound (x * y) (b₁ * b₂) := by
  by_cases h : (b₁ * b₂) ≥ n
  . apply Fin_Bound_ge (Fin_Bound_modulus (x * y)) h
  simp at h
  rcases h₁ with h₁ | h₁
  . rcases h₂ with h₂ | h₂
    . left
      rw [Fin.val_mul]
      apply le_trans (Nat.mod_le (x.val * y.val) n)
      trans x.val * b₂
      . apply mul_le_mul_left' h₂
      . apply mul_le_mul_right' h₁
    . apply Fin_bound_mul_helper h h₁ h₂
  . rcases h₂ with h₂ | h₂
    . nth_rw 2 [mul_comm]
      rw [mul_comm]
      rw [mul_comm] at h
      apply Fin_bound_mul_helper h h₂ h₁
    . left
      by_cases g : n = 0
      . omega
      have g : NeZero n := ⟨by omega⟩
      generalize hx : Fin.sub n x = x'
      generalize hy : Fin.sub n y = y'
      have h3 : x + x' = 0 := by
        rw [← hx]; simp
        show x + (0 - x) = 0
        simp
      have h4 : y + y' = 0 := by
        rw [← hy]; simp
        show y + (0 - y) = 0
        simp
      have h5 : x * y = x' * y' := by
        have : x * y = (x + x') * (y + y') + x' * y' - x' * (y + y') - y' * (x + x') := by
          ring
        rw [this, h3, h4]
        ring
      rw [h5, Fin.val_mul]
      apply le_trans (Nat.mod_le (x'.val * y'.val) n)
      trans x'.val * b₂
      . apply mul_le_mul_left'
        rw [←hy, Fin.sub, Fin.val]; simp
        apply le_trans (Nat.mod_le (n - ↑y) n)
        simp
        linarith
      . apply mul_le_mul_right'
        rw [←hx, Fin.sub, Fin.val]; simp
        apply le_trans (Nat.mod_le (n - ↑x) n)
        simp
        linarith

lemma Fin_bound_dotprod {p m b₁ b₂ : ℕ} {v₁ v₂ : Vector (Fin p) m}
(h1 : Fin_Bound_vec v₁ b₁) (h2 : Fin_Bound_vec v₂ b₂) (Nez : NeZero p) :
  Fin_Bound (dotProduct v₁.get v₂.get) (b₁ * b₂ * m) := by
  rw [dotProduct]
  generalize hf : (fun i ↦ v₁.get i * v₂.get i) = f
  have : ∀ i, Fin_Bound (f i) (b₁ * b₂) := by
    intro i
    simp_rw [← hf]
    apply Fin_Bound_mul (h1 i) (h2 i)
  generalize hb : b₁ * b₂ = b
  rw [hb] at this
  clear hf hb h1 h2 v₁ v₂ b₁ b₂
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.univ_castSuccEmb]
    simp
    rw [Finset.sum_insert, add_comm]
    . apply Fin_Bound_add
      . simp
        apply ih
        intro i
        rw [Fin.castLE]
        apply this
      . apply this
    simp
    intro ⟨i, hi⟩ hl
    rw [Fin.castLE, Fin.last] at hl
    simp at hl
    linarith

lemma Fin_bound_castLE {n m : ℕ} {x : Fin n} {h : n ≤ m} :
  Fin_Bound (Fin.castLE h x) n := by
  left; simp

lemma Fin_bound_shift_cast_vec {p χ m : ℕ} {v : Vector (Fin (2*χ + 1)) m}
 {hne : NeZero p} (h : p > 2*χ) : Fin_Bound_vec (v.map (fun t ↦ (Fin.castLE h t) - (Fin.ofNat' p χ))) χ := by
  intro i
  simp [Vector.get]
  by_cases n0 : χ = 0
  . have := Fin.le_val_last (v[i])
    simp [n0] at *
    trivial
  by_cases hv : v[i] ≥ χ
  . left
    simp at *
    sorry
  . sorry
  --   have : NeZero χ := ⟨by omega⟩
  --   have : χ < p := by omega
  --   conv =>
  --     rhs
  --     rw [← (Nat.mod_eq_of_lt this), ← Fin.val_ofNat']
  --   apply Fin.natCast_le_natCast
  --   . simp

  --   apply Fin.val_lt_of_le (Fin.castLE h (v.get i))
  --   simp [hv]
  --   apply Fin.val_lt_of_le (Fin.castLE h (v.get i))
  --   apply Fin.sub_lt
  --   . apply Fin.val_lt_of_le (Fin.castLE h (v.get i))
  --   . simp [Fin.ofNat', Fin.castLE]
  --     apply Nat.le_sub_left_iff_add_le.mpr
  --     apply Nat.le_sub_left_iff_add_le.mp
  --     apply Nat.add_le_add_right hv χ
  -- . right
  --   apply Fin.val_lt_of_le (Fin.castLE h (v.get i))
  --   apply Fin.sub_lt
  --   . simp [Fin.ofNat', Fin.castLE]
  --     apply Nat.le_sub_left_iff_add_le.mpr
  --     apply Nat.le_sub_left_iff_add_le.mp
  --     apply Nat.add_le_add_right hv χ
  --   . simp [Fin.ofNat', Fin.castLE]
  --     apply Nat.le_sub_left_iff_add_le.mpr
  --     apply Nat.le_sub_left_iff_add_le.mp
  --     apply Nat.add_le_add_right hv χ

end useful_lemmas

namespace Regev

variable (n m χ p : ℕ) (h: NeZero p) (herr: p > 2*χ) (hp2 : p > 1)

section sound

theorem isCorrect : (regevAsymmEnc n m χ p herr hp2).PerfectlyCorrect := by
  rintro msg
  simp [CorrectExp, regevAsymmEnc]
  rintro A s e r
  generalize h1 : (Vector.map (Fin.castLE hp2) r).get = rv
  have pne0 : NeZero p := ⟨by omega⟩
  simp
  rw [← Matrix.dotProduct_mulVec]
  cases msg <;> simp
  . constructor
    . ring_nf
      sorry
    . sorry
  . sorry

end sound

end Regev
