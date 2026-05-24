/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Presentation
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Diagonal pushout of a colimit presentation

For a colimit presentation `P : ColimitPresentation ι X`, the diagonal pushout
functor sends `i ↦ pushout (P.ι.app i) (P.ι.app i)`. It is used to compare the
binary tensor square of a filtered colimit with the filtered colimit of binary
tensor squares.

We also add the standard reduction simp lemmas for `pushout.inl ≫ pushout.map`
and `pushout.inr ≫ pushout.map`, which are not yet in Mathlib.

## Main definitions

* `CategoryTheory.Limits.ColimitPresentation.diagPushout`: the diagonal pushout
  functor associated to a colimit presentation.
-/

universe t w v u

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- Precomposing `pushout.map` with `pushout.inl` recovers `i₁ ≫ pushout.inl`. -/
@[reassoc (attr := simp)]
lemma pushout_inl_map {X Y Z X' Y' Z' : C}
    (f : Z ⟶ X) (g : Z ⟶ Y) [HasPushout f g]
    (f' : Z' ⟶ X') (g' : Z' ⟶ Y') [HasPushout f' g']
    (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : Z ⟶ Z')
    (e₁ : f ≫ i₁ = i₃ ≫ f') (e₂ : g ≫ i₂ = i₃ ≫ g') :
    pushout.inl f g ≫ pushout.map f g f' g' i₁ i₂ i₃ e₁ e₂ = i₁ ≫ pushout.inl f' g' :=
  pushout.inl_desc _ _ _

/-- Precomposing `pushout.map` with `pushout.inr` recovers `i₂ ≫ pushout.inr`. -/
@[reassoc (attr := simp)]
lemma pushout_inr_map {X Y Z X' Y' Z' : C}
    (f : Z ⟶ X) (g : Z ⟶ Y) [HasPushout f g]
    (f' : Z' ⟶ X') (g' : Z' ⟶ Y') [HasPushout f' g']
    (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : Z ⟶ Z')
    (e₁ : f ≫ i₁ = i₃ ≫ f') (e₂ : g ≫ i₂ = i₃ ≫ g') :
    pushout.inr f g ≫ pushout.map f g f' g' i₁ i₂ i₃ e₁ e₂ = i₂ ≫ pushout.inr f' g' :=
  pushout.inr_desc _ _ _

namespace ColimitPresentation

variable [HasPushouts C]
variable {ι : Type w} [Category.{t} ι] {X : C} (P : ColimitPresentation ι X)

/-- The diagonal pushout diagram associated to a colimit presentation:
`i ↦ pushout (P.ι.app i) (P.ι.app i)`. -/
@[simps]
noncomputable def diagPushout : ι ⥤ C where
  obj i := pushout (P.ι.app i) (P.ι.app i)
  map {i j} h :=
    pushout.map (P.ι.app i) (P.ι.app i) (P.ι.app j) (P.ι.app j)
      (𝟙 X) (𝟙 X) (P.diag.map h)
      ((Category.comp_id _).trans (P.w h).symm) ((Category.comp_id _).trans (P.w h).symm)
  map_id i := by apply pushout.hom_ext <;> simp
  map_comp {i j k} f g := by
    apply pushout.hom_ext
    · simp [pushout.map_comp]
    · simp [pushout.map_comp]

@[reassoc (attr := simp)]
lemma diagPushout_inl_map {i j : ι} (h : i ⟶ j) :
    pushout.inl (P.ι.app i) (P.ι.app i) ≫ P.diagPushout.map h =
      pushout.inl (P.ι.app j) (P.ι.app j) := by
  rw [P.diagPushout_map]
  exact (pushout.inl_desc _ _ _).trans (Category.id_comp _)

@[reassoc (attr := simp)]
lemma diagPushout_inr_map {i j : ι} (h : i ⟶ j) :
    pushout.inr (P.ι.app i) (P.ι.app i) ≫ P.diagPushout.map h =
      pushout.inr (P.ι.app j) (P.ι.app j) := by
  rw [P.diagPushout_map]
  exact (pushout.inr_desc _ _ _).trans (Category.id_comp _)

end ColimitPresentation

end CategoryTheory.Limits
