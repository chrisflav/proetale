/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Proetale.Algebra.StalkIso
import Proetale.Mathlib.Algebra.Category.CommAlgCat.Limits
import Proetale.Mathlib.CategoryTheory.Limits.Presentation

/-!
# Filtered colimits of `R`-algebras and bijectivity on stalks

If `S = colim_i Aᵢ` is a filtered colimit of `R`-algebras and each `R → Aᵢ` is bijective on
stalks, then so is `R → S`.
-/

universe u

open CategoryTheory Limits

namespace CategoryTheory.Limits.ColimitPresentation

variable {R : Type u} [CommRing R] {X : CommAlgCat.{u} R}
variable {ι : Type u} [SmallCategory ι]

/-- For a colimit presentation in `CommAlgCat R`, the colimit injection at the target composed
with the diagram map equals the colimit injection at the source. -/
lemma ι_app_diag_map_apply (P : ColimitPresentation ι X) {i j : ι} (f : i ⟶ j) (x : P.diag.obj i) :
    (P.ι.app j).hom ((P.diag.map f).hom x) = (P.ι.app i).hom x :=
  DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (P.w f)) x

end CategoryTheory.Limits.ColimitPresentation

namespace Algebra.BijectiveOnStalks

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type u} [SmallCategory ι]
variable (P : ColimitPresentation ι (CommAlgCat.of R S))

/-- The contraction of an ideal `p` of the colimit `S` to a constituent `P.diag.obj i`. -/
private noncomputable def colimitPrime (p : Ideal S) (i : ι) : Ideal (P.diag.obj i) :=
  p.comap (P.ι.app i).hom.toRingHom

private instance (p : Ideal S) [p.IsPrime] (i : ι) : (colimitPrime P p i).IsPrime :=
  Ideal.IsPrime.comap _

private lemma colimitPrime_comap_algebraMap (p : Ideal S) (i : ι) :
    p.comap (algebraMap R S) =
      (colimitPrime P p i).comap (algebraMap R (P.diag.obj i)) := by
  ext r
  rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap, ← (P.ι.app i).hom.commutes r]
  rfl

private lemma colimitPrime_comap_diag (p : Ideal S) {i j : ι} (f : i ⟶ j) :
    colimitPrime P p i = (colimitPrime P p j).comap (P.diag.map f).hom.toRingHom := by
  ext r
  rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap,
    ← ColimitPresentation.ι_app_diag_map_apply P f r]
  rfl

variable (p : Ideal S) [p.IsPrime]

/-- The diagram of localizations `Localization.AtPrime (colimitPrime P p i)` for `i : ι`, with
transition maps given by `Localization.localRingHom`. -/
private noncomputable def localizationDiag : ι ⥤ CommRingCat.{u} where
  obj i := .of (Localization.AtPrime (colimitPrime P p i))
  map {i j} f := CommRingCat.ofHom <| Localization.localRingHom _ _
    (P.diag.map f).hom.toRingHom (colimitPrime_comap_diag P p f)
  map_id i := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun x ↦ ?_
    obtain ⟨⟨r, s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective
      (colimitPrime P p i).primeCompl x
    simp [Localization.localRingHom_mk']
  map_comp {i j k} f g := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun x ↦ ?_
    obtain ⟨⟨r, s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective
      (colimitPrime P p i).primeCompl x
    simp [Localization.localRingHom_mk', P.diag.map_comp]

/-- The cocone over `localizationDiag P p` with apex `Localization.AtPrime p`. -/
private noncomputable def localizationCocone : Cocone (localizationDiag P p) where
  pt := .of (Localization.AtPrime p)
  ι :=
    { app i := CommRingCat.ofHom <|
        Localization.localRingHom (colimitPrime P p i) p (P.ι.app i).hom.toRingHom rfl
      naturality {i j} f := by
        apply CommRingCat.hom_ext
        refine RingHom.ext fun x ↦ ?_
        obtain ⟨⟨r, s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective
          (colimitPrime P p i).primeCompl x
        simp only [Functor.const_obj_obj, Functor.const_obj_map, localizationDiag,
          CommRingCat.hom_comp, CommRingCat.hom_id, CommRingCat.hom_ofHom,
          RingHom.id_apply, RingHom.comp_apply, Localization.localRingHom_mk']
        refine congrArg₂ (IsLocalization.mk' _) ?_ (Subtype.ext ?_)
        · exact ColimitPresentation.ι_app_diag_map_apply P f r
        · exact ColimitPresentation.ι_app_diag_map_apply P f s }

variable [IsFiltered ι]

/-- Every element of `Localization.AtPrime p` lifts to an element of
`Localization.AtPrime (colimitPrime P p i)` for some `i : ι`. -/
private lemma exists_localRingHom_eq (z : Localization.AtPrime p) :
    ∃ (i : ι) (zᵢ : Localization.AtPrime (colimitPrime P p i)),
      Localization.localRingHom (colimitPrime P p i) p
        (P.ι.app i).hom.toRingHom rfl zᵢ = z := by
  obtain ⟨⟨s, u, hu⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
  obtain ⟨i₁, s₀, hs₀⟩ := Concrete.isColimit_exists_rep _ P.isColimit s
  obtain ⟨i₂, u₀, hu₀⟩ := Concrete.isColimit_exists_rep _ P.isColimit u
  let i : ι := IsFiltered.max i₁ i₂
  let s' : P.diag.obj i := (P.diag.map (IsFiltered.leftToMax i₁ i₂)).hom s₀
  let u' : P.diag.obj i := (P.diag.map (IsFiltered.rightToMax i₁ i₂)).hom u₀
  have hs' : (P.ι.app i).hom s' = s :=
    (ColimitPresentation.ι_app_diag_map_apply P _ s₀).trans hs₀
  have hu' : (P.ι.app i).hom u' = u :=
    (ColimitPresentation.ι_app_diag_map_apply P _ u₀).trans hu₀
  refine ⟨i, IsLocalization.mk' _ s' ⟨u', fun hmem ↦ hu (hu' ▸ hmem)⟩, ?_⟩
  rw [Localization.localRingHom_mk']
  exact congrArg₂ (IsLocalization.mk' _) hs' (Subtype.ext hu')

/-- If two elements of `Localization.AtPrime (colimitPrime P p i)` have equal images in
`Localization.AtPrime p`, they become equal in `Localization.AtPrime (colimitPrime P p k)` for
some `f : i ⟶ k`. -/
private lemma exists_eq_of_localRingHomDiag_eq (i : ι)
    (x y : Localization.AtPrime (colimitPrime P p i))
    (hxy : Localization.localRingHom (colimitPrime P p i) p
        (P.ι.app i).hom.toRingHom rfl x =
      Localization.localRingHom (colimitPrime P p i) p
        (P.ι.app i).hom.toRingHom rfl y) :
    ∃ (k : ι) (f : i ⟶ k),
      Localization.localRingHom (colimitPrime P p i) (colimitPrime P p k)
          (P.diag.map f).hom.toRingHom (colimitPrime_comap_diag P p f) x =
        Localization.localRingHom (colimitPrime P p i) (colimitPrime P p k)
          (P.diag.map f).hom.toRingHom (colimitPrime_comap_diag P p f) y := by
  obtain ⟨⟨r₁, s₁, hs₁⟩, rfl⟩ := IsLocalization.mk'_surjective
    (colimitPrime P p i).primeCompl x
  obtain ⟨⟨r₂, s₂, hs₂⟩, rfl⟩ := IsLocalization.mk'_surjective
    (colimitPrime P p i).primeCompl y
  rw [Localization.localRingHom_mk', Localization.localRingHom_mk'] at hxy
  obtain ⟨⟨c, hcp⟩, hc⟩ := (IsLocalization.eq (S := Localization.AtPrime p)).mp hxy
  obtain ⟨k₀, c', hc'⟩ := Concrete.isColimit_exists_rep _ P.isColimit c
  let i' : ι := IsFiltered.max i k₀
  let li : i ⟶ i' := IsFiltered.leftToMax i k₀
  let rk : k₀ ⟶ i' := IsFiltered.rightToMax i k₀
  let c'' : P.diag.obj i' := (P.diag.map rk).hom c'
  have hkey :
      (P.ι.app i').hom (c'' * ((P.diag.map li).hom s₂ * (P.diag.map li).hom r₁)) =
        (P.ι.app i').hom (c'' * ((P.diag.map li).hom s₁ * (P.diag.map li).hom r₂)) := by
    simpa [map_mul, ColimitPresentation.ι_app_diag_map_apply, c'', hc'] using hc
  obtain ⟨k, fij, hjeq⟩ := (IsColimit.eq_iff' P.isColimit _ _).mp hkey
  refine ⟨k, li ≫ fij, ?_⟩
  have hck_to_c : (P.ι.app k).hom ((P.diag.map fij).hom c'') = c := by
    rw [ColimitPresentation.ι_app_diag_map_apply, c'',
      ColimitPresentation.ι_app_diag_map_apply, hc']
  have hcomp (z : P.diag.obj i) :
      (P.diag.map fij).hom ((P.diag.map li).hom z) = (P.diag.map (li ≫ fij)).hom z := by
    rw [P.diag.map_comp]; rfl
  rw [Localization.localRingHom_mk', Localization.localRingHom_mk', IsLocalization.eq]
  refine ⟨⟨(P.diag.map fij).hom c'', fun hmem ↦ hcp (hck_to_c ▸ hmem)⟩, ?_⟩
  simpa [map_mul, hcomp] using hjeq

/-- The localization of a filtered colimit at a prime `p` is the colimit of the localizations
`Localization.AtPrime (colimitPrime P p i)`. -/
private noncomputable def isColimitLocalizationCocone : IsColimit (localizationCocone P p) := by
  have : ReflectsFilteredColimits (forget CommRingCat.{u}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  refine isColimitOfReflects (forget _)
    (Types.FilteredColimit.isColimitOf' (localizationDiag P p ⋙ forget _)
      ((forget _).mapCocone (localizationCocone P p)) ?_ ?_)
  · intro z
    obtain ⟨i, zᵢ, hzᵢ⟩ := exists_localRingHom_eq P p z
    exact ⟨i, zᵢ, hzᵢ.symm⟩
  · intro i x y hxy
    exact exists_eq_of_localRingHomDiag_eq P p i x y hxy

omit p [p.IsPrime] in
/-- If `S` is a filtered colimit of `R`-algebras `Aᵢ` and each `R → Aᵢ` is bijective on
stalks, then so is `R → S`. -/
lemma of_colimitPresentation
    (h : ∀ i, Algebra.BijectiveOnStalks R (P.diag.obj i)) :
    Algebra.BijectiveOnStalks R S := by
  obtain ⟨i₀⟩ : Nonempty ι := IsFiltered.nonempty
  refine ⟨fun p hp ↦ ⟨?_, ?_⟩⟩
  · intro x y hxy
    set g₀ : Localization.AtPrime (p.comap (algebraMap R S)) →+*
        Localization.AtPrime (colimitPrime P p i₀) :=
      Localization.localRingHom (p.comap (algebraMap R S)) (colimitPrime P p i₀)
        (algebraMap R (P.diag.obj i₀)) (colimitPrime_comap_algebraMap P p i₀) with hg₀
    set ι₀ : Localization.AtPrime (colimitPrime P p i₀) →+* Localization.AtPrime p :=
      Localization.localRingHom (colimitPrime P p i₀) p (P.ι.app i₀).hom.toRingHom rfl with hι₀
    have hcomp : ι₀.comp g₀ =
        Localization.localRingHom (p.comap (algebraMap R S)) p (algebraMap R S) rfl := by
      rw [hg₀, hι₀, ← Localization.localRingHom_comp]
      congr 1
      exact (P.ι.app i₀).hom.comp_algebraMap
    have hxy' : ι₀ (g₀ x) = ι₀ (g₀ y) := by
      rw [← RingHom.comp_apply, ← RingHom.comp_apply, hcomp]
      exact hxy
    obtain ⟨k, fij, hdiag⟩ := exists_eq_of_localRingHomDiag_eq P p i₀ (g₀ x) (g₀ y) hxy'
    have hk_comp :
        (Localization.localRingHom (colimitPrime P p i₀) (colimitPrime P p k)
          (P.diag.map fij).hom.toRingHom (colimitPrime_comap_diag P p fij)).comp g₀ =
        Localization.localRingHom (p.comap (algebraMap R S)) (colimitPrime P p k)
          (algebraMap R (P.diag.obj k)) (colimitPrime_comap_algebraMap P p k) := by
      rw [hg₀, ← Localization.localRingHom_comp]
      congr 1
      exact (P.diag.map fij).hom.comp_algebraMap
    apply ((RingHom.bijectiveOnStalks_algebraMap.mpr (h k)).localRingHom_of_eq
      (colimitPrime_comap_algebraMap P p k)).1
    rw [← hk_comp, RingHom.comp_apply, RingHom.comp_apply]
    exact hdiag
  · intro z
    obtain ⟨i, zᵢ, rfl⟩ := exists_localRingHom_eq P p z
    obtain ⟨w, rfl⟩ :=
      ((RingHom.bijectiveOnStalks_algebraMap.mpr (h i)).localRingHom_of_eq
        (colimitPrime_comap_algebraMap P p i)).2 zᵢ
    refine ⟨w, ?_⟩
    obtain ⟨⟨r, s, hs⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (p.comap (algebraMap R S)).primeCompl w
    rw [Localization.localRingHom_mk', Localization.localRingHom_mk', Localization.localRingHom_mk']
    refine congrArg₂ (IsLocalization.mk' _) ?_ (Subtype.ext ?_)
    · exact ((P.ι.app i).hom.commutes r).symm
    · exact ((P.ι.app i).hom.commutes s).symm

end Algebra.BijectiveOnStalks
