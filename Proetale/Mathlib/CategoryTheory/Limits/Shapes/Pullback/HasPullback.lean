/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Simp lemmas for `pushout.inl ≫ pushout.map` and `pushout.inr ≫ pushout.map`

These are the natural simp companions of `pushout.map_comp` and `pushout.map_id`
and should be upstreamed to Mathlib alongside the dual `pullback.map_fst` /
`pullback.map_snd`.
-/

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- Precomposing `pushout.map` with `pushout.inl` recovers `i₁ ≫ pushout.inl`. -/
@[reassoc (attr := simp)]
lemma pushout.inl_map {X Y Z X' Y' Z' : C}
    (f : Z ⟶ X) (g : Z ⟶ Y) [HasPushout f g]
    (f' : Z' ⟶ X') (g' : Z' ⟶ Y') [HasPushout f' g']
    (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : Z ⟶ Z')
    (e₁ : f ≫ i₁ = i₃ ≫ f') (e₂ : g ≫ i₂ = i₃ ≫ g') :
    pushout.inl f g ≫ pushout.map f g f' g' i₁ i₂ i₃ e₁ e₂ = i₁ ≫ pushout.inl f' g' :=
  pushout.inl_desc _ _ _

/-- Precomposing `pushout.map` with `pushout.inr` recovers `i₂ ≫ pushout.inr`. -/
@[reassoc (attr := simp)]
lemma pushout.inr_map {X Y Z X' Y' Z' : C}
    (f : Z ⟶ X) (g : Z ⟶ Y) [HasPushout f g]
    (f' : Z' ⟶ X') (g' : Z' ⟶ Y') [HasPushout f' g']
    (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : Z ⟶ Z')
    (e₁ : f ≫ i₁ = i₃ ≫ f') (e₂ : g ≫ i₂ = i₃ ≫ g') :
    pushout.inr f g ≫ pushout.map f g f' g' i₁ i₂ i₃ e₁ e₂ = i₂ ≫ pushout.inr f' g' :=
  pushout.inr_desc _ _ _

end CategoryTheory.Limits
