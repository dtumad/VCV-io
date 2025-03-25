import Iris
import Iris.Algebra.CMRA
import ToMathlib.ProbabilityTheory.Coupling

/-! # Formalizing the Bluebell paper -/

open Iris ProbabilityTheory MeasureTheory

-- Indexed tuples
def indexedTuple (α : Type*) (I : Finset ℕ) := I → α

def indexedTuple.remove (α : Type*) (I : Finset ℕ) (J : Finset ℕ) (h : J ⊆ I) :
    indexedTuple α I → indexedTuple α (I \ J) :=
  fun x i => x ⟨i.1, by aesop⟩

/-- A typeclass for expressing that a type `M` has a validity predicate `✓` -/
class Valid (M : Type*) where
  valid : M → Prop

prefix:50 "✓" => Valid.valid

instance {α : Type*} [Valid α] (p : α → Prop) : Valid (Subtype p) where
  valid := fun x => Valid.valid x.1

instance {α β : Type*} [Valid α] [Valid β] : Valid (α × β) where
  valid := fun x => Valid.valid x.1 ∧ Valid.valid x.2

/-- The class of **discrete** cameras, which do not care about step-indexing -/
class DiscreteCMRA (α : Type*) extends CommSemigroup α, Valid α where
  equiv : α → α → Prop
  pcore : α → Option α

  is_equiv : Equivalence equiv

  mul_equiv {x y z} : equiv y z → equiv (x * y) (x * z)
  pcore_equiv {x y cx} : equiv x y → pcore x = some cx → ∃ cy, pcore y = some cy ∧ equiv cx cy

  pcore_left {x cx} : pcore x = some cx → equiv (cx * x) x
  pcore_idem {x cx} : pcore x = some cx → equiv x cx
  pcore_mono' {x y cx} : pcore x = some cx → ∃ cy, pcore (x * y) = some (cx * cy)

  -- TODO: check whether these are stated correctly
  valid_equiv {x y} : equiv x y → valid x → valid y
  valid_mul_left {x y} : valid (x * y) → valid x
  valid_extend {x y₁ y₂} : valid x → equiv x (y₁ * y₂) → ∃ z₁ z₂, equiv x (z₁ * z₂) ∧ valid z₁ ∧ valid z₂

-- /-- A discrete CMRA can be converted to a regular CMRA -/
instance DiscreteCMRA.instCMRA (α : Type*) [DiscreteCMRA α] : CMRA α := sorry

-- class DiscreteUnitalCMRA (α : Type*) extends DiscreteCMRA α, One α where

/-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
`1 * a = a` on the left.

This is a unbundled version of `MulOneClass` where we don't require `a * 1 = a` on the right. -/
class MulOneLeftClass (M : Type*) extends One M, Mul M where
  /-- One is a left neutral element for multiplication -/
  protected one_mul : ∀ a : M, 1 * a = a

attribute [simp] MulOneLeftClass.one_mul

instance {M : Type*} [MulOneClass M] : MulOneLeftClass M where
  one_mul := one_mul

/-- An **ordered unital resource algebra** is a type with a multiplication, a one, a preorder `≤`,
  and a validity predicate `✓`, such that `1` is valid, validity is closed under multiplication
  and the preorder, and left multiplication is monotone. -/
class OrderedUnitalResourceAlgebra (M : Type*) extends MulOneLeftClass M, Valid M, Preorder M where
  valid_one : ✓ (1 : M)
  valid_mul {a b} : ✓ a → ✓ b → ✓ (a * b : M)
  valid_mono {a b} : a ≤ b → ✓ b → ✓ (a : M)
  mul_left_mono {a b c} : a ≤ b → a * c ≤ (b * c : M)

/-- Define a discrete `CMRA` instance given an `OrderedUnitalResourceAlgebra` instance -/
instance OrderedUnitalResourceAlgebra.instCMRA {M : Type*} [OrderedUnitalResourceAlgebra M] :
    DiscreteCMRA M := sorry


/-! ## Permissions -/

/-- A permission on type `α` is a map from `α` to the non-negative rationals `ℚ≥0`.

We need to have the `Multiplicative` tag in order to specify that multiplication is pointwise
addition, and unit is the constant zero map. -/
@[reducible] def Permission (α : Type*) := Multiplicative (α → ℚ≥0)

variable {α : Type*}

-- instance : Preorder (Permission α) := inferInstanceAs (Preorder (Multiplicative (α → ℚ≥0)))
-- instance : MulOneClass (Permission α) := inferInstanceAs (MulOneClass (Multiplicative (α → ℚ≥0)))
-- instance : MulLeftMono (Permission α) := inferInstanceAs (MulLeftMono (Multiplicative (α → ℚ≥0)))

/-- Permissions form an `OrderedUnitalResourceAlgebra` where `≤` is defined pointwise, a resource is valid iff it's below `1` pointwise, and composition is pointwise multiplication -/
instance : OrderedUnitalResourceAlgebra (Permission α) where
  valid := fun p => p ≤ 1
  valid_one := by simp
  valid_mul := by intro a b ha hb; simp_all only [le_one_iff_eq_one, mul_one, le_refl]
  valid_mono := by intro a b h h'; simp_all only [le_one_iff_eq_one]
  mul_left_mono := by intro a b c h i; sorry


/-! ## Probability stuff -/

/-- A measure space is a tuple of a measurable space and a measure on it. This is essentially the
  bundled version of `Measure` -/
def MeasureTuple (Ω : Type*) := (ℱ : MeasurableSpace Ω) × Measure[ℱ] Ω

/-- A probability space is a `MeasureTuple` where the measure is a probability measure (i.e. has
  total measure `1`) -/
def ProbabilitySpace (Ω : Type*) := (ℱ : MeasurableSpace Ω) × {μ : Measure[ℱ] Ω // IsProbabilityMeasure μ}

variable {Ω : Type*}

def MeasureTuple.σAlg (m : MeasureTuple Ω) : MeasurableSpace Ω := m.1
def MeasureTuple.μ (m : MeasureTuple Ω) : Measure[m.1] Ω := m.2

@[simp]
lemma MeasureTuple.σAlg_apply (m : MeasureTuple Ω) : MeasureTuple.σAlg m = m.1 := rfl
@[simp]
lemma MeasureTuple.μ_apply (m : MeasureTuple Ω) : MeasureTuple.μ m = m.2 := rfl

def ProbabilitySpace.σAlg (m : ProbabilitySpace Ω) : MeasurableSpace Ω := m.1
def ProbabilitySpace.μ (m : ProbabilitySpace Ω) : Measure[m.1] Ω := m.2.1

@[simp]
lemma ProbabilitySpace.σAlg_apply (m : ProbabilitySpace Ω) : ProbabilitySpace.σAlg m = m.1 := rfl
@[simp]
lemma ProbabilitySpace.μ_apply (m : ProbabilitySpace Ω) : ProbabilitySpace.μ m = m.2.1 := rfl

/-- We define `(ℱ, μ) ≤ (𝒢, ν)` if `ℱ ≤ 𝒢` and `μ` is the restriction of `ν` to `ℱ` -/
instance : Preorder (MeasureTuple Ω) where
  -- TODO: double-check if we are supposed to use `map` or `comap`
  le m₁ m₂ := (m₁.σAlg ≤ m₂.σAlg) ∧ m₁.μ = (@Measure.map _ _ m₂.σAlg m₁.σAlg id m₂.μ)
  le_refl m := by simp only [LE.le, imp_self, implies_true, Measure.map_id, and_self]
  le_trans := by
    rintro ⟨ℱ₁, μ₁⟩ ⟨ℱ₂, μ₂⟩ ⟨ℱ₃, μ₃⟩ ⟨hℱ₁₂, hμ₁₂⟩ ⟨hℱ₂₃, hμ₂₃⟩
    simp_all
    refine ⟨le_trans hℱ₁₂ hℱ₂₃, ?_⟩
    · rw [Measure.map_map] <;> aesop

/-- We define `(ℱ, μ) ≤ (𝒢, ν)` if `ℱ ≤ 𝒢` and `μ` is the restriction of `ν` to `ℱ` -/
instance : Preorder (ProbabilitySpace Ω) where
  le m₁ m₂ := (m₁.σAlg ≤ m₂.σAlg) ∧ m₁.μ = (@Measure.map _ _ m₂.σAlg m₁.σAlg id m₂.μ)
  le_refl m := by simp only [LE.le, imp_self, implies_true, Measure.map_id, and_self]
  le_trans := by
    rintro ⟨ℱ₁, ⟨μ₁, _⟩⟩ ⟨ℱ₂, ⟨μ₂, _⟩⟩ ⟨ℱ₃, ⟨μ₃, _⟩⟩ ⟨hℱ₁₂, hμ₁₂⟩ ⟨hℱ₂₃, hμ₂₃⟩
    simp_all
    refine ⟨le_trans hℱ₁₂ hℱ₂₃, ?_⟩
    · rw [Measure.map_map] <;> aesop

/-- The sum of two measurable spaces on the same space `Ω` is the measurable space generated by the
  union of the two spaces -/
def MeasurableSpace.sum (m₁ : MeasurableSpace Ω) (m₂ : MeasurableSpace Ω) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom (MeasurableSet[m₁] ∪ MeasurableSet[m₂])

variable {m₁ : MeasurableSpace Ω} {m₂ : MeasurableSpace Ω}

/-- An independent product of measures `μ₁` and `μ₂` (on measurable spaces `m₁` and `m₂`,
    respectively) is a measure `μ` on the sum of `m₁` and `m₂` that satisfies the product formula -/
@[ext]
class Measure.IndependentProduct (μ₁ : Measure[m₁] Ω) (μ₂ : Measure[m₂] Ω) where
  μ : Measure[MeasurableSpace.sum m₁ m₂] Ω
  inter_eq_prod {X Y} (hX : MeasurableSet[m₁] X) (hY : MeasurableSet[m₂] Y) :
    μ (X ∩ Y) = μ₁ X * μ₂ Y

/-- The independent product of two measures is unique, if it exists -/
instance {μ₁ : Measure[m₁] Ω} {μ₂ : Measure[m₂] Ω} : Subsingleton (Measure.IndependentProduct μ₁ μ₂) := by
  constructor
  intro ⟨μ, hμ⟩ ⟨μ', hμ'⟩
  ext
  simp
  sorry
  -- To prove this, [Li et al. 2023] requires the Dynkin π-λ theorem

noncomputable section

/-- The partial operation of independent product on `MeasureTuple`s, when it exists -/
def MeasureTuple.indepProduct (m₁ : MeasureTuple Ω) (m₂ : MeasureTuple Ω) : Option (MeasureTuple Ω) := by
  classical
  by_cases h : Nonempty (Measure.IndependentProduct m₁.2 m₂.2)
  · exact some ⟨MeasurableSpace.sum m₁.1 m₂.1, (Classical.choice h).μ⟩
  · exact none

def ProbabilitySpace.indepProduct (m₁ : ProbabilitySpace Ω) (m₂ : ProbabilitySpace Ω) : Option (ProbabilitySpace Ω) := by
  classical
  by_cases h : Nonempty (Measure.IndependentProduct m₁.2.1 m₂.2.1)
  · exact some ⟨MeasurableSpace.sum m₁.1 m₂.1, ⟨(Classical.choice h).μ, by sorry⟩⟩
  · exact none

-- We want the trivial `{∅, Ω}` sigma algebra, upon which the measure is defined to be `0` on `∅`
-- and `1` on `Ω`
instance [inst : Nonempty Ω] : One (ProbabilitySpace Ω) where
  one := ⟨⊥, ⟨@Measure.dirac _ ⊥ (Classical.choice inst), by constructor; simp [Measure.dirac]⟩⟩

abbrev PSp (Ω : Type*) := WithTop (ProbabilitySpace Ω)

@[simp]
instance : Valid (PSp Ω) where
  valid := fun x => match x with | some _ => True | none => False

instance [inst : Nonempty Ω] : OrderedUnitalResourceAlgebra (PSp Ω) where
  mul := fun x y => match x, y with
    | some x, some y => if h : (x.indepProduct y).isSome then (x.indepProduct y).get h else none
    | _, _ => none
  valid_one := by simp
  -- There seems to be a problem here: if `a = some x`, `b = some y`, but `x.indepProduct y = none`,
  -- then `a` is valid but `a * b = ⊤` is not
  valid_mul := by intro a b ha hb; cases a <;> cases b <;> simp_all; sorry
  valid_mono := by intro a b _ _; cases a <;> cases b <;> simp_all
  one_mul := sorry
  mul_left_mono := sorry

variable {V : Type*}

-- Needs to encode the term `P = P' ⊗ 𝟙_ (p.support → V)` in the paper
def ProbabilitySpace.compatiblePerm (_P : ProbabilitySpace (α → V)) (p : Permission α) : Prop :=
  ∃ _P' : ProbabilitySpace ({a // p a > 0} → V), True

/-- Generalize compatibility to `PSp` by letting `⊤` be compatible with all permission maps -/
def PSp.compatiblePerm (P : PSp (α → V)) (p : Permission α) : Prop := match P with
  | some P => ProbabilitySpace.compatiblePerm P p
  | none => True

@[reducible]
def PSpPm (α : Type*) (V : Type*) :=
  {Pp : PSp (α → V) × Permission α // Pp.1.compatiblePerm Pp.2}

@[simp]
instance [Nonempty V] : One (PSpPm α V) where
  one := ⟨⟨One.one, One.one⟩, by simp [One.one, PSp.compatiblePerm, ProbabilitySpace.compatiblePerm]⟩

/-- Multiplication is pointwise product of the probability space and the permission -/
@[simp]
instance [Nonempty V] : Mul (PSpPm α V) where
  -- TODO: need to prove product preserves compatibility
  mul Pp₁ Pp₂ := ⟨⟨Pp₁.1.1 * Pp₂.1.1, Pp₁.1.2 * Pp₂.1.2⟩, by sorry⟩

-- instance : Valid (PSpPm α V) := inferInstanceAs <|
--   Valid (Subtype (fun Pp : PSp (α → V) × Permission α => Pp.1.compatiblePerm Pp.2))

instance [Nonempty V] : OrderedUnitalResourceAlgebra (PSpPm α V) where
  one_mul := by simp; intro P p h; sorry
  valid_one := by simp [Valid.valid, One.one]; sorry
  valid_mul := by sorry
  valid_mono := by sorry
  mul_left_mono := by sorry

-- To handle multiple programs drawn from index set `I : Finset ℕ`, we use the RA `I → PSpPm` where
-- operations are lifted pointwise

-- (Hyper-)assertions are defined as `(I → PSpPm) -[upward closed]→ Prop`

end
