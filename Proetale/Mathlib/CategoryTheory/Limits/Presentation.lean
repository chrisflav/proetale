/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Presentation
import Mathlib.CategoryTheory.Limits.Connected
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
* `CategoryTheory.Limits.ColimitPresentation.isColimitDiagPushout`: for a connected index
  category, the codiagonal cocone exhibits `X` as the colimit of `diagPushout`.

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
  map_comp {i j k} f g := by ext <;> simp [pushout.map_comp]

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

/-- The codiagonal cocone on the diagonal pushout diagram, with cocone point `X` and
`app i = pushout.desc (𝟙 X) (𝟙 X)`. -/
@[simps]
noncomputable def diagPushoutCocone : P.diagPushout ⟶ (Functor.const ι).obj X where
  app i := pushout.desc (𝟙 X) (𝟙 X) rfl
  naturality {i j} h := by
    dsimp [diagPushout]
    apply pushout.hom_ext
    all_goals
      simp only [← Category.assoc, pushout.inl_desc, pushout.inr_desc,
        Category.id_comp, Category.comp_id]

variable [IsConnected ι]

/-- For a cocone `s` over the diagonal pushout diagram with `ι` connected, the morphism
`pushout.inl _ _ ≫ s.ι.app i : X ⟶ s.pt` does not depend on `i`. -/
lemma diagPushout_inl_app_eq (s : Cocone P.diagPushout) (i j : ι) :
    pushout.inl (P.ι.app i) (P.ι.app i) ≫ s.ι.app i =
      pushout.inl (P.ι.app j) (P.ι.app j) ≫ s.ι.app j := by
  refine constant_of_preserves_morphisms
    (fun k ↦ pushout.inl (P.ι.app k) (P.ι.app k) ≫ s.ι.app k) (fun a b f ↦ ?_) i j
  simp only [← s.w f, P.diagPushout_inl_map_assoc]

/-- For a cocone `s` over the diagonal pushout diagram with `ι` connected, the morphism
`pushout.inr _ _ ≫ s.ι.app i : X ⟶ s.pt` does not depend on `i`. -/
lemma diagPushout_inr_app_eq (s : Cocone P.diagPushout) (i j : ι) :
    pushout.inr (P.ι.app i) (P.ι.app i) ≫ s.ι.app i =
      pushout.inr (P.ι.app j) (P.ι.app j) ≫ s.ι.app j := by
  refine constant_of_preserves_morphisms
    (fun k ↦ pushout.inr (P.ι.app k) (P.ι.app k) ≫ s.ι.app k) (fun a b f ↦ ?_) i j
  simp only [← s.w f, P.diagPushout_inr_map_assoc]

/-- The cocone over `P.diag` with point `s.pt` induced by a cocone `s` over the diagonal
pushout diagram, via the left pushout inclusion. -/
noncomputable def diagPushoutCoconeDescAux (s : Cocone P.diagPushout) : Cocone P.diag where
  pt := s.pt
  ι :=
    { app := fun i ↦ P.ι.app i ≫ pushout.inl _ _ ≫ s.ι.app i
      naturality := fun {i j} f ↦ by
        dsimp
        rw [Category.comp_id, P.diagPushout_inl_app_eq s j i, ← Category.assoc, P.w f] }

/-- The codiagonal cocone over the diagonal pushout diagram is a colimit when `ι` is connected.

This is the special case of "connected colimits commute with pushouts" for the span
`X ← P.diag.obj i → X`: the colimit of `i ↦ pushout (P.ι.app i) (P.ι.app i)` is again `X`. -/
noncomputable def isColimitDiagPushout :
    IsColimit (Cocone.mk X P.diagPushoutCocone) where
  desc s := P.isColimit.desc (P.diagPushoutCoconeDescAux s)
  fac s i := by
    apply pushout.hom_ext
    · simp only [diagPushoutCocone_app, pushout.inl_desc_assoc]
      refine P.isColimit.hom_ext fun k ↦ ?_
      rw [P.isColimit.fac]
      show P.ι.app k ≫ pushout.inl (P.ι.app k) (P.ι.app k) ≫ s.ι.app k = _
      rw [P.diagPushout_inl_app_eq s k i]
    · simp only [diagPushoutCocone_app, pushout.inr_desc_assoc]
      refine P.isColimit.hom_ext fun k ↦ ?_
      rw [P.isColimit.fac]
      show P.ι.app k ≫ pushout.inl (P.ι.app k) (P.ι.app k) ≫ s.ι.app k =
        P.ι.app k ≫ pushout.inr (P.ι.app i) (P.ι.app i) ≫ s.ι.app i
      rw [P.diagPushout_inr_app_eq s i k]
      simp only [← Category.assoc, pushout.condition]
  uniq s m hm := by
    have hm' : ∀ i, pushout.desc (𝟙 X) (𝟙 X) rfl ≫ m = s.ι.app i := hm
    refine P.isColimit.hom_ext fun i ↦ ?_
    rw [P.isColimit.fac]
    show P.ι.app i ≫ m = P.ι.app i ≫ pushout.inl (P.ι.app i) (P.ι.app i) ≫ s.ι.app i
    rw [← hm' i, pushout.inl_desc_assoc]
    simp

end ColimitPresentation

end CategoryTheory.Limits
