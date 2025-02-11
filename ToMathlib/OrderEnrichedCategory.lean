import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.Order.Category.Preord
import Mathlib.Order.Monotone.Basic

open CategoryTheory

/-! # Order enriched category

We show that the general definition of an enriched category over a monoidal category specializes to
an order-enriched category when the monoidal category is the category of preorders.
-/

/-- The category of preorders is monoidal. -/
instance : MonoidalCategory (Preord) where
  tensorObj X Y := Bundled.of (X × Y)
  whiskerLeft X Y := fun f => ⟨fun x => (x.1, f.1 x.2),
      (by simp [Monotone, Bundled.of]; intro _ _ _ _ h h'; exact ⟨h, f.2 h'⟩)⟩
  whiskerRight f Y := ⟨fun y => (f.1 y.1, y.2),
      (by simp [Monotone, Bundled.of]; intro _ _ _ _ h h'; exact ⟨f.2 h, h'⟩)⟩
  tensorUnit := Bundled.of PUnit
  -- /-- The associator isomorphism `(X ⊗ Y) ⊗ Z ≃ X ⊗ (Y ⊗ Z)` -/
  associator X Y Z := {
    hom := ⟨fun ⟨⟨x, y⟩, z⟩ => ⟨x, ⟨y, z⟩⟩, by
      simp only [Monotone, Bundled.of, Prod.mk_le_mk, Prod.forall, and_imp]
      intro _ _ _ _ _ _ h1 h2 h3; exact ⟨h1, h2, h3⟩⟩
    inv := ⟨fun ⟨x, ⟨y, z⟩⟩ => ⟨⟨x, y⟩, z⟩, by
      simp only [Monotone, Bundled.of, Prod.mk_le_mk, Prod.forall, and_imp]
      intro _ _ _ _ _ _ h1 h2 h3; exact ⟨⟨h1, h2⟩, h3⟩⟩ }
  leftUnitor X := {
    hom := ⟨Prod.snd, (by simp [Monotone, Bundled.of])⟩
    inv := ⟨fun x => ((), x), by simp [Monotone, Bundled.of]⟩ }
  rightUnitor X := {
    hom := ⟨Prod.fst, (by simp [Monotone, Bundled.of])⟩
    inv := ⟨fun x => (x, ()), by simp [Monotone, Bundled.of]⟩ }
  tensorHom_def f g := rfl
  tensor_id _ _ := rfl
  tensor_comp f₁ f₂ g₁ g₂ := rfl
  whiskerLeft_id _ _ := rfl
  id_whiskerRight _ _ := rfl
  associator_naturality f₁ f₂ f₃ := rfl
  leftUnitor_naturality f := rfl
  rightUnitor_naturality f := rfl
  pentagon _ _ _ _ := rfl
  triangle _ _ := rfl
