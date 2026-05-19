/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-!
# `HasOfPostcompProperty` from a cancellation property of ring homs

We generalize `AlgebraicGeometry.HasRingHomProperty.of_comp`: instead of requiring the universal
cancellation `Q (g.comp f) → Q g`, we allow a second ring hom property `Q'` and a scheme
morphism property `W` such that
* `W g` implies `Q' g.appTop.hom` for affine `g`,
* `Q` cancels left with `Q'`: `Q' f → Q (g.comp f) → Q g`.

Under these hypotheses, `P` has the `HasOfPostcompProperty` with respect to `W`.
-/

universe u

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry.HasRingHomProperty

variable {P : MorphismProperty Scheme.{u}}
  {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
  [HasRingHomProperty P Q]

/-- Generalization of `HasRingHomProperty.of_comp`: if `Q` cancels left with `Q'`, the scheme
property `W` is local at the target, gives `Q'` on global sections for affine source and target,
and is preserved under pre-composition with open immersions, then `P` has the of-postcomp
property with respect to `W`. -/
theorem hasOfPostcompProperty
    (W : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget W]
    {Q' : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hQQ' : ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
      (f : R →+* S) (g : S →+* T), Q' f → Q (g.comp f) → Q g)
    (hW : ∀ {Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z] {g : Y ⟶ Z},
      W g → Q' g.appTop.hom)
    (hW_comp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {g : Y ⟶ Z},
      W g → W (f ≫ g)) :
    P.HasOfPostcompProperty W where
  of_postcomp {X Y Z} f g hg h := by
    wlog hZ : IsAffine Z generalizing X Y Z
    · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _
        (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
      intro U
      have h' : P ((f ∣_ (g ⁻¹ᵁ U.1)) ≫ (g ∣_ U.1)) := by
        simpa [morphismRestrict_comp] using IsZariskiLocalAtTarget.restrict h U.1
      exact this _ _ (IsZariskiLocalAtTarget.restrict hg U.1) h' U.2
    wlog hY : IsAffine Y generalizing X Y
    · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top Y)]
      intro U
      have h' : P ((f ∣_ U.1) ≫ (U.1.ι ≫ g)) := by
        simpa [morphismRestrict_ι_assoc, Category.assoc] using
          comp_of_isOpenImmersion P (f ⁻¹ᵁ U.1).ι (f ≫ g) h
      exact this _ _ (hW_comp U.1.ι hg) h' U.2
    wlog hX : IsAffine X generalizing X
    · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top X)]
      intro U
      have h' : P (U.1.ι ≫ f ≫ g) := comp_of_isOpenImmersion P U.1.ι (f ≫ g) h
      rw [← Category.assoc] at h'
      exact this _ h' U.2
    rw [iff_of_isAffine (P := P)] at h ⊢
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at h
    exact hQQ' _ _ (hW hg) h

end AlgebraicGeometry.HasRingHomProperty
