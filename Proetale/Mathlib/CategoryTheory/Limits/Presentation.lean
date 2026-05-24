/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Presentation
import Proetale.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Diagonal pushout of a colimit presentation

For a colimit presentation `P : ColimitPresentation ι X`, the diagonal pushout
functor sends `i ↦ pushout (P.ι.app i) (P.ι.app i)`. It is used to compare a
binary pushout of a filtered colimit with the filtered colimit of binary
pushouts.

## Main definitions

* `CategoryTheory.Limits.ColimitPresentation.diagPushout`: the diagonal pushout
  functor associated to a colimit presentation.

## TODO

`diagPushout` is the diagonal special case of a more general construction:
given `α β : F ⟶ G` between functors `J ⥤ C` (with `G = (Functor.const J).obj X`
fixed here), one obtains the functor `i ↦ pushout (α.app i) (β.app i)`. The
general version can be added without renaming `diagPushout`.
-/

universe t w v u

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

namespace ColimitPresentation

variable {ι : Type w} [Category.{t} ι] {X : C} (P : ColimitPresentation ι X)
variable [∀ i, HasPushout (P.ι.app i) (P.ι.app i)]

/-- The diagonal pushout diagram associated to a colimit presentation:
`i ↦ pushout (P.ι.app i) (P.ι.app i)`. -/
@[simps]
noncomputable def diagPushout : ι ⥤ C where
  obj i := pushout (P.ι.app i) (P.ι.app i)
  map {i j} h :=
    pushout.map (P.ι.app i) (P.ι.app i) (P.ι.app j) (P.ι.app j)
      (𝟙 X) (𝟙 X) (P.diag.map h)
      (by simp) (by simp)
  map_id i := by ext <;> simp
  map_comp {i j k} f g := by
    apply pushout.hom_ext
    · simp [pushout.map_comp]
    · simp [pushout.map_comp]

@[reassoc (attr := simp)]
lemma diagPushout_inl_map {i j : ι} (h : i ⟶ j) :
    pushout.inl (P.ι.app i) (P.ι.app i) ≫ P.diagPushout.map h =
      pushout.inl (P.ι.app j) (P.ι.app j) := by
  simp

@[reassoc (attr := simp)]
lemma diagPushout_inr_map {i j : ι} (h : i ⟶ j) :
    pushout.inr (P.ι.app i) (P.ι.app i) ≫ P.diagPushout.map h =
      pushout.inr (P.ι.app j) (P.ι.app j) := by
  simp

end ColimitPresentation

end CategoryTheory.Limits
