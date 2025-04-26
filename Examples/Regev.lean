import VCVio

open Mathlib OracleSpec OracleComp AsymmEncAlg

-- #check AtLeastTwo
lemma relax_p_bound {p χ m: ℕ} (h : p > 4 * (χ * m + 1)) (hm : 1 ≤ m) : p > 2 * χ := by
  calc p > 4 * (χ * m + 1) := h
  _ ≥ 4 * (χ * m) := by ring_nf; omega
  _ ≥ 2 * (χ * m) := by ring_nf; omega
  _ ≥ 2 * χ := by
    apply Nat.mul_le_mul_left (2*χ) at hm
    ring_nf at hm ⊢; omega

/-- The uniform error sampling distribution, from the range `[-χ, χ]` inside `Fin p` -/
def uniformErrSamp {p : ℕ} [NeZero p] (χ : ℕ) (herr : p > 2*χ) : ProbComp (Fin p) := do
  let e ←$ᵗ Fin (2*χ + 1)
  return (Fin.castLE herr e) - χ

-- TODO: refactor the error sampling to use `uniformErrSamp` instead
def regevAsymmEnc (n m χ p : ℕ) (he: p > 4*(χ*m + 1)) (hm: 1 ≤ m) (hp2 : p > 1) : AsymmEncAlg ProbComp
    (M := Bool) (PK := Matrix (Fin n) (Fin m) (Fin p) × Vector (Fin p) m)
     (SK := Vector (Fin p) n) (C := Vector (Fin p) n × Fin p) where
  keygen := do
    have : NeZero p := ⟨by omega⟩
    have herr: p > 2*χ := (relax_p_bound he hm)
    let A ←$ᵗ Matrix (Fin n) (Fin m) (Fin p)
    let s ←$ᵗ Vector (Fin p) n
    let e ←$ᵗ Vector (Fin (2*χ + 1)) m
    let err := e.map (fun t ↦ (Fin.castLE herr t) - χ)
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
      linarith [x.isLt]
  . left; linarith

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
        linarith [y.isLt]
      . right
        simp [Fin.val_add_eq_ite, h]
        omega
  . rcases h₂ with h₂ | h₂
    . by_cases h : n ≤ x.val + y.val
      . left
        simp [Fin.val_add_eq_ite, h]
        linarith [x.isLt]
      . right
        simp [Fin.val_add_eq_ite, h]
        linarith [x.isLt]
    . right
      rw [Fin.val_add_eq_ite]
      by_cases h : n ≤ x.val + y.val <;> simp [h] <;> omega

lemma Fin_bound_mul_helper {n b₁ b₂ : ℕ} {x y : Fin n} (h : b₁ * b₂ < n)
  (h₁ : x.val ≤ b₁) (h₂ : y.val + b₂ ≥ n) : Fin_Bound (x * y) (b₁ * b₂) := by
  by_cases g : x.val = 0
  . left; simp [Fin.val_mul, g]
  right
  rw [Fin.val_mul]
  have hy : y.val < n := y.isLt
  have hc : ∃ c ≤ b₂, y.val + c = n := by
    use n - y.val; constructor <;> omega
  rcases hc with ⟨c, hc1, hc2⟩
  have h3 : x.val * y.val + x.val * c = n * x.val := by
    rw [← mul_add, hc2]; apply mul_comm
  calc x.val * y.val % n + b₁ * b₂ ≥ x.val * y.val % n + b₁ * b₂ := by rfl
    _ ≥ x.val * y.val % n + b₁ * c :=
      Nat.add_le_add_left (Nat.mul_le_mul_left b₁ hc1) _
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

@[simp]
lemma Fin_bound_neg {n b : ℕ} {x : Fin n} (h : Fin_Bound x b) :
  Fin_Bound (-x) b := by
  by_cases h0 : n = 0
  . rw [h0] at x
    apply x.elim0
  have nnz : NeZero n := ⟨by omega⟩
  have : Fin_Bound (-(Fin.ofNat' n 1)) 1 := by
    right
    simp [Fin.coe_neg]
    by_cases h1 : n = 1
    . simp [h1]
    push_neg at h0 h1
    rw [Nat.one_mod_eq_one.mpr h1]
    rw [Nat.mod_eq_of_lt] <;> omega
  rw [← one_mul b, ← neg_one_mul x]
  apply Fin_Bound_mul this h

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

@[simp]
lemma Fin_bound_castLE {n m : ℕ} {x : Fin (n + 1)} {h : n < m} :
  Fin_Bound (Fin.castLE h x) n := by
  left; simp; omega

lemma IntLE_imp_NatLE {a b : ℕ} (h : (a : ℤ) ≤ (b : ℤ)) : a ≤ b := by
  omega

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
    apply IntLE_imp_NatLE
    rw [Fin.intCast_val_sub_eq_sub_add_ite]
    simp
    have : ↑χ ≤ Fin.castLE h v[↑i] := by
      simp [hv]
      rw [Fin.le_def] at hv ⊢
      trans ↑v[i] <;> simp at *
      rw [Nat.mod_eq_of_lt] at hv ⊢ <;> omega
    simp at this
    simp [this]
    trans 2 * χ
    . norm_cast
      have g := Fin.val_lt_of_le v[↑i] (le_refl (2*χ + 1))
      omega
    . rw [Int.ofNat_mod_ofNat, Nat.mod_eq_of_lt]
      linarith
      linarith
  . right
    simp at *
    apply IntLE_imp_NatLE; simp
    rw [Fin.intCast_val_sub_eq_sub_add_ite]; simp
    have : ↑χ > Fin.castLE h v[↑i] := by
      simp [hv]
      rw [Fin.lt_def] at hv ⊢
      apply lt_of_le_of_lt
      simp at *
      apply le_refl
      simp at *
      rw [Nat.mod_eq_of_lt] at hv ⊢
      trivial
      omega
      omega
    rw [ite_cond_eq_false]
    . rw [Int.ofNat_mod_ofNat, Nat.mod_eq_of_lt]
      linarith
      linarith
    simp at this
    simp [this]

end useful_lemmas

namespace Regev

variable (n m χ p : ℕ) (h: NeZero p) (he: p > 4*(χ*m + 1)) (hp2 : p > 1) (hm : 1 ≤ m)

section correct

theorem isCorrect : (regevAsymmEnc n m χ p he hm hp2).PerfectlyCorrect := by
  rintro msg
  simp [CorrectExp, regevAsymmEnc]
  rintro A s e r
  generalize h1 : (Vector.map (Fin.castLE hp2) r) = rv
  have pne0 : NeZero p := ⟨by omega⟩
  have herr: p > 2*χ := (relax_p_bound he hm)
  simp
  rw [← Matrix.dotProduct_mulVec]
  generalize h2 : (Vector.map (fun t ↦ Fin.castLE herr t - ↑χ) e) = err
  generalize h3 : -(err.get ⬝ᵥ rv.get) = mask
  have : χ * m ≤ p / 4 - 1:= by
    simp at he
    rw [mul_comm] at he
    apply le_of_lt at he
    have : 0 < 4 := by linarith
    apply (Nat.le_div_iff_mul_le this).2 at he
    omega
  have mask_bound : Fin_Bound mask (χ * m) := by
    rw [← mul_one χ, ← h3, ← h2, ← h1]
    apply Fin_bound_neg
    apply Fin_bound_dotprod
    . apply Fin_bound_shift_cast_vec
    . intro i
      simp [Vector.get]
  apply Fin_Bound_ge mask_bound at this
  cases msg <;> simp
  . constructor <;> ring_nf <;> rw [h3] <;>
    rcases this with h | h <;> rw [Fin.sub_def, Fin.val] <;> simp
    . rw [Nat.mod_eq_of_lt]
      . rw [Nat.mod_eq_of_lt] <;> omega
      rw [Nat.mod_eq_of_lt] <;> omega
    . rw [Nat.mod_eq_sub_mod]
      . rw [Nat.mod_eq_of_lt] <;> rw [Nat.mod_eq_of_lt] <;> omega
      rw [Nat.mod_eq_of_lt] <;> omega
    . rw [Nat.mod_eq_of_lt]
      . rw [Nat.mod_eq_of_lt] <;> omega
      rw [Nat.mod_eq_of_lt] <;> omega
    . rw [Nat.mod_eq_sub_mod]
      . rw [Nat.mod_eq_of_lt] <;> rw [Nat.mod_eq_of_lt] <;> omega
      rw [Nat.mod_eq_of_lt] <;> omega
  . rw [h3]
    rcases this with h | h
    . left; omega
    . right; omega

end correct

section security

-- Original hybrid (hybrid 0) is the IND-CPA experiment

variable {n m χ p} {he hp2 hm}
  -- (lwe_adv : Matrix (Fin n) (Fin m) (Fin p) × Vector (Fin p) m → ProbComp Bool)
  (adv : IND_CPA_Adv (regevAsymmEnc n m χ p he hm hp2))

-- noncomputable def LWE_Advantage : ℝ :=
--   (LWE_Experiment n m p (uniformErrSamp χ (by sorry)) adv).advantage

-- Want to show:
-- ∀ adv in hybrid 0,
  -- advantage (hybrid 0, adv) ≤ advantage (hybrid 1, reduction1 (adv)) + advantage (LWE game, ...)
-- ∀ adv in hybrid 1, advantage (hybrid 1, adv) ≤ advantage (hybrid 2, reduction2 (adv))

def Regev_Hybrid_0 : ProbComp Unit := IND_CPA_OneTime_Game (encAlg := regevAsymmEnc n m χ p he hm hp2) adv

example : Regev_Hybrid_0 adv = IND_CPA_OneTime_Game (encAlg := regevAsymmEnc n m χ p he hm hp2) adv := by
  rfl
  -- simp [IND_CPA_OneTime_Game, regevAsymmEnc]

-- What Hybrid 0 looks like:
-- do
--   let b ← $ᵗBool
--   let x ← $ᵗMatrix (Fin n) (Fin m) (Fin p)
--   let x_1 ← $ᵗVector (Fin p) n
--   let a ← $ᵗVector (Fin (2 * χ + 1)) m
--   let __discr ←
--     adv.chooseMessages (x, Vector.ofFn (Matrix.vecMul x_1.get x) + Vector.map (fun t ↦ Fin.castLE ⋯ t - ↑χ) a)
--   let a_1 ← $ᵗVector (Fin 2) m
--   let b' ←
--     adv.distinguish __discr.2.2
--         (Vector.ofFn (x.mulVec (Vector.map (Fin.castLE hp2) a_1).get),
--           Matrix.vecMul x_1.get x ⬝ᵥ (Vector.map (Fin.castLE hp2) a_1).get +
--               (Vector.map (fun t ↦ Fin.castLE ⋯ t - ↑χ) a).get ⬝ᵥ (Vector.map (Fin.castLE hp2) a_1).get +
--             if if b = true then __discr.1 = true else __discr.2.1 = true then 0 else ↑(p / 2))
--   if b = b' then pure () else failure

-- In Hybrid 1, we sample u = A s + e randomly instead
def Regev_Hybrid_1 : ProbComp Unit := do
  let b ←$ᵗ Bool
  let A ←$ᵗ Matrix (Fin n) (Fin m) (Fin p)
  let u ←$ᵗ Vector (Fin p) m
  let ⟨m₁, m₂, st⟩ ← adv.chooseMessages (A, u)
  let c ← if b then (regevAsymmEnc n m χ p he hm hp2).encrypt (A, u) m₁
    else (regevAsymmEnc n m χ p he hm hp2).encrypt (A, u) m₂
  let b' ← adv.distinguish st c
  guard (b = b')

-- Hybrid 0 and Hybrid 1 are indistinguishable due to decisional LWE

def Regev_Hybrid_2 : ProbComp Unit := do
  let b ←$ᵗ Bool
  let A ←$ᵗ Matrix (Fin n) (Fin m) (Fin p)
  let u ←$ᵗ Vector (Fin p) m
  let ⟨_, _, st⟩ ← adv.chooseMessages (A, u)
  -- Don't know why have to sample `c₁` and `c₂` separately
  let c₁ ←$ᵗ Vector (Fin p) n
  let c₂ ←$ᵗ Fin p
  let b' ← adv.distinguish st (c₁, c₂)
  guard (b = b')

-- Hybrid 1 and Hybrid 2 are indistinguishable due to the leftover hash lemma (or LWE itself)

-- def IND_CPA_regev_lwe_reduction (b : Bool)
--     (adversary : (regevAsymmEnc n m χ p he hm hp2).IND_CPA_Adv) :
--     Matrix (Fin n) (Fin m) (Fin p) × Vector (Fin p) m → ProbComp Bool := fun ⟨A, v⟩ => do
--   let so : QueryImpl (Bool × Bool →ₒ (Vector (Fin p) n) × (Fin p)) ProbComp := ⟨fun (query () (m₁, m₂)) =>
--     (regevAsymmEnc n m χ p he hm hp2).encrypt ⟨A, v⟩ (if b then m₁ else m₂)⟩
--   simulateQ (idOracle ++ₛₒ so) (adversary.distinguish (⟨A, v⟩))

-- theorem Regev_IND_CPA {encAlg : AsymmEncAlg (OracleComp spec) M PK SK C}
--     {adv : IND_CPA_Adv (spec := spec) encAlg} :
--     IND_CPA_Advantage adv ≤ LWE_Advantage (Reduction adv) := by sorry

-- Want to show:
-- ∀ adv in hybrid 0,
  -- advantage (hybrid 0, adv) ≤ advantage (hybrid 1, reduction1 (adv)) + advantage (LWE game, ...)
-- ∀ adv in hybrid 1, advantage (hybrid 1, adv) ≤ advantage (hybrid 2, reduction2 (adv))

end security

end Regev
