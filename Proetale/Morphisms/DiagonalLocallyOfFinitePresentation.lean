import Mathlib

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

theorem LocallyOfFinitePresentation.of_comp_locallyOfFiniteType {X Y Z : Scheme} (f : X ⟶ Y)
    (g : Y ⟶ Z) [hfg : LocallyOfFinitePresentation (f ≫ g)] [hg : LocallyOfFiniteType g] :
    LocallyOfFinitePresentation f :=
  have aux {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : LocallyOfFinitePresentation (f ≫ g))
      (hg : LocallyOfFiniteType g) : LocallyOfFinitePresentation f := by
    wlog hZ : IsAffine Z generalizing X Y Z f g
    · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
        (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
      intro U
      have h : LocallyOfFinitePresentation ((f ∣_ (g ⁻¹ᵁ U.1)) ≫ (g ∣_ U.1)) := by
        simpa [morphismRestrict_comp] using IsZariskiLocalAtTarget.restrict hfg U.1
      exact this (f ∣_ (g ⁻¹ᵁ U.1)) (g ∣_ U.1) h (IsZariskiLocalAtTarget.restrict hg U.1) U.2
    wlog hY : IsAffine Y generalizing X Y f g
    · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
        (iSup_affineOpens_eq_top Y)]
      intro U
      have h : LocallyOfFinitePresentation ((f ∣_ U.1) ≫ (U.1.ι ≫ g)) := by
        simpa [morphismRestrict_ι_assoc, Category.assoc] using
          HasRingHomProperty.comp_of_isOpenImmersion @LocallyOfFinitePresentation
            (f ⁻¹ᵁ U.1).ι (f ≫ g) hfg
      exact this (f ∣_ U.1) (U.1.ι ≫ g) h (locallyOfFiniteType_comp U.1.ι g) U.2
    wlog hX : IsAffine X generalizing X f g
    · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
        (iSup_affineOpens_eq_top X)]
      intro U
      have h : LocallyOfFinitePresentation (U.1.ι ≫ f ≫ g) := by
        simpa [Category.assoc] using
          HasRingHomProperty.comp_of_isOpenImmersion @LocallyOfFinitePresentation U.1.ι (f ≫ g) hfg
      exact this (U.1.ι ≫ f) g h hg U.2
    have hcomp : RingHom.FinitePresentation (f.appTop.hom.comp g.appTop.hom) := by
      simpa [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
        (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).1 hfg
    exact HasRingHomProperty.iff_of_isAffine.2 <|
      RingHom.FinitePresentation.of_comp_finiteType g.appTop.hom hcomp <|
        HasRingHomProperty.iff_of_isAffine.1 hg
  aux f g hfg hg

theorem diagonal_locallyOfFinitePresentation {X Y : Scheme} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] : LocallyOfFinitePresentation (pullback.diagonal f) :=
  have : LocallyOfFinitePresentation (pullback.diagonal f ≫ pullback.fst f f) := by
    simpa only [pullback.diagonal_fst f] using locallyOfFinitePresentation_of_isOpenImmersion (𝟙 X)
  LocallyOfFinitePresentation.of_comp_locallyOfFiniteType (pullback.diagonal f) (pullback.fst f f)

end AlgebraicGeometry
