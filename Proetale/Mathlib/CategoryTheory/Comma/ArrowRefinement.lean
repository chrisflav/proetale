/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Refining a cofiltered category by a property of its arrows

Let `J` be a cofiltered category and `Φ` a property of arrows of `J` that is

- closed under precomposition: if `Φ u` and `a : l' ⟶ l`, then `Φ (a ≫ u)`, and
- attainable: for every `k : J` there exists `w : m ⟶ k` with `Φ w`.

We show that the full subcategory `A` of `Arrow J` spanned by `Φ` is cofiltered and that both
projections `A ⥤ J` (domain and codomain) are initial.

This is the index category used to refine a level-wise presentation of a morphism of pro-objects
into one whose levels satisfy a "spreading" property (e.g. surjectivity of pulled-back covers):
the object `u : l ⟶ k` of `A` indexes the data "level `l` of the base together with a deeper
level `k` at which the property has been achieved".
-/

universe v u

namespace CategoryTheory

open Limits

variable {J : Type u} [Category.{v} J] (Φ : ObjectProperty (Arrow J))

namespace ArrowRefinement

/-- A morphism `Arrow.mk h ⟶ v` in `Arrow J` from components and a commuting square. -/
@[simps]
def arrowHomMk {l k : J} (h : l ⟶ k) (v : Arrow J) (x : l ⟶ v.left) (y : k ⟶ v.right)
    (w : x ≫ v.hom = h ≫ y) : Arrow.mk h ⟶ v where
  left := x
  right := y
  w := by simpa using w

/-- A morphism `Arrow.mk (𝟙 l₀) ⟶ v` in `Arrow J` from any `x : l₀ ⟶ v.left`. -/
@[simps!]
def arrowHomMkId {l₀ : J} (v : Arrow J) (x : l₀ ⟶ v.left) : Arrow.mk (𝟙 l₀) ⟶ v :=
  arrowHomMk (𝟙 l₀) v x (x ≫ v.hom) (by simp)

variable (hpre : ∀ {l' l k : J} (a : l' ⟶ l) (u : l ⟶ k), Φ (Arrow.mk u) → Φ (Arrow.mk (a ≫ u)))

section

variable [IsCofiltered J]
variable (hex : ∀ k : J, ∃ (m : J) (w : m ⟶ k), Φ (Arrow.mk w))

include hpre hex

/-- Any arrow of `J` receives a morphism (in `Arrow J`) from an arrow satisfying `Φ`. -/
lemma exists_hom (v : Arrow J) :
    ∃ u : Φ.FullSubcategory, Nonempty (u.obj ⟶ v) := by
  obtain ⟨m, w, hw⟩ := hex v.right
  let l := IsCofiltered.min m v.left
  let p : l ⟶ m := IsCofiltered.minToLeft _ _
  let q : l ⟶ v.left := IsCofiltered.minToRight _ _
  let e := IsCofiltered.eqHom (p ≫ w) (q ≫ v.hom)
  have he := IsCofiltered.eq_condition (p ≫ w) (q ≫ v.hom)
  exact ⟨⟨Arrow.mk (e ≫ p ≫ w), hpre e (p ≫ w) (hpre p w hw)⟩,
    ⟨arrowHomMk _ v (e ≫ q) (𝟙 v.right) (by simpa using he.symm)⟩⟩

lemma isCofilteredOrEmpty : IsCofilteredOrEmpty Φ.FullSubcategory where
  cone_objs u₁ u₂ := by
    -- a cone over the pair via the trivial arrow on `min` of the two sources
    let l₀ := IsCofiltered.min u₁.obj.left u₂.obj.left
    let a₁ : l₀ ⟶ u₁.obj.left := IsCofiltered.minToLeft _ _
    let a₂ : l₀ ⟶ u₂.obj.left := IsCofiltered.minToRight _ _
    obtain ⟨u, ⟨f⟩⟩ := exists_hom Φ hpre hex (Arrow.mk (𝟙 l₀))
    exact ⟨u, InducedCategory.homMk (f ≫ arrowHomMkId u₁.obj a₁),
      InducedCategory.homMk (f ≫ arrowHomMkId u₂.obj a₂), trivial⟩
  cone_maps u₁ u₂ f g := by
    -- equalize the left components; the right components then agree automatically
    let e := IsCofiltered.eqHom f.hom.left g.hom.left
    have he : e ≫ f.hom.left = e ≫ g.hom.left := IsCofiltered.eq_condition _ _
    obtain ⟨u, ⟨m⟩⟩ := exists_hom Φ hpre hex
      (Arrow.mk (𝟙 (IsCofiltered.eq f.hom.left g.hom.left)))
    have hr : (e ≫ u₁.obj.hom) ≫ f.hom.right = (e ≫ u₁.obj.hom) ≫ g.hom.right := by
      rw [Category.assoc, ← Arrow.w f.hom, Category.assoc, ← Arrow.w g.hom,
        ← Category.assoc, ← Category.assoc, he]
    refine ⟨u, InducedCategory.homMk (m ≫ arrowHomMkId u₁.obj e), ?_⟩
    ext
    · simpa using m.left ≫= he
    · simpa using m.right ≫= hr

lemma isCofiltered : IsCofiltered Φ.FullSubcategory :=
  letI := isCofilteredOrEmpty Φ hpre hex
  haveI : Nonempty Φ.FullSubcategory := by
    obtain ⟨k⟩ := IsCofiltered.nonempty (C := J)
    obtain ⟨m, w, hw⟩ := hex k
    exact ⟨⟨Arrow.mk w, hw⟩⟩
  { }

/-- The domain projection from the refinement category is initial. -/
lemma initial_leftFunc :
    (Φ.ι ⋙ Arrow.leftFunc : Φ.FullSubcategory ⥤ J).Initial := by
  letI := isCofiltered Φ hpre hex
  apply Functor.initial_of_exists_of_isCofiltered
  · intro d
    obtain ⟨u, ⟨f⟩⟩ := exists_hom Φ hpre hex (Arrow.mk (𝟙 d))
    exact ⟨u, ⟨f.left⟩⟩
  · intro d u s s'
    let e := IsCofiltered.eqHom s s'
    have he : e ≫ s = e ≫ s' := IsCofiltered.eq_condition _ _
    obtain ⟨u', ⟨m⟩⟩ := exists_hom Φ hpre hex (Arrow.mk (𝟙 (IsCofiltered.eq s s')))
    refine ⟨u', InducedCategory.homMk (m ≫ arrowHomMkId u.obj e), ?_⟩
    simpa using m.left ≫= he

/-- The codomain projection from the refinement category is initial. -/
lemma initial_rightFunc :
    (Φ.ι ⋙ Arrow.rightFunc : Φ.FullSubcategory ⥤ J).Initial := by
  letI := isCofiltered Φ hpre hex
  apply Functor.initial_of_exists_of_isCofiltered
  · intro d
    obtain ⟨m, w, hw⟩ := hex d
    exact ⟨⟨Arrow.mk w, hw⟩, ⟨𝟙 d⟩⟩
  · intro d u s s'
    let e := IsCofiltered.eqHom s s'
    have he : e ≫ s = e ≫ s' := IsCofiltered.eq_condition _ _
    -- build an arrow into `u.obj` whose right component is `e`
    let l₀ := IsCofiltered.min u.obj.left (IsCofiltered.eq s s')
    let p : l₀ ⟶ u.obj.left := IsCofiltered.minToLeft _ _
    let q : l₀ ⟶ IsCofiltered.eq s s' := IsCofiltered.minToRight _ _
    let e' := IsCofiltered.eqHom (p ≫ u.obj.hom) (q ≫ e)
    have he' := IsCofiltered.eq_condition (p ≫ u.obj.hom) (q ≫ e)
    obtain ⟨u', ⟨m⟩⟩ := exists_hom Φ hpre hex (Arrow.mk (e' ≫ q))
    refine ⟨u', InducedCategory.homMk
      (m ≫ arrowHomMk (e' ≫ q) u.obj (e' ≫ p) e (by simpa using he')), ?_⟩
    simpa using m.right ≫= he

end

end ArrowRefinement

end CategoryTheory
