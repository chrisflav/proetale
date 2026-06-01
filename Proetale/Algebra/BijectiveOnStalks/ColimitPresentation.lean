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
stalks, then so is `R → S`. The argument goes through the fact that the localization of `S`
at a prime `p` is the filtered colimit of the localizations of the `Aᵢ` at `p ∩ Aᵢ`.
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

section ColimitPresentation

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type u} [SmallCategory ι]
  (P : ColimitPresentation ι (CommAlgCat.of R S))

/-- The contraction of an ideal `p` of the colimit `S` to a constituent `P.diag.obj i`. -/
private noncomputable def colimitPrime (p : Ideal S) (i : ι) : Ideal (P.diag.obj i) :=
  p.comap (P.ι.app i).hom.toRingHom

private instance (p : Ideal S) [p.IsPrime] (i : ι) : (colimitPrime P p i).IsPrime :=
  Ideal.IsPrime.comap _

private lemma colimitPrime_comap_algebraMap (p : Ideal S) (i : ι) :
    p.comap (algebraMap R S) =
      (colimitPrime P p i).comap (algebraMap R (P.diag.obj i)) := by
  have hcomm (r : R) :
      (P.ι.app i).hom (algebraMap R (P.diag.obj i) r) = algebraMap R S r :=
    (P.ι.app i).hom.commutes r
  ext r
  simp only [Ideal.mem_comap, colimitPrime, ← hcomm r]
  rfl

private lemma colimitPrime_comap_diag (p : Ideal S) {i j : ι} (f : i ⟶ j) :
    colimitPrime P p i = (colimitPrime P p j).comap (P.diag.map f).hom.toRingHom := by
  ext r
  change (P.ι.app i).hom r ∈ p ↔ (P.ι.app j).hom ((P.diag.map f).hom r) ∈ p
  rw [ColimitPresentation.ι_app_diag_map_apply P f r]

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
    rw [CommRingCat.hom_ofHom, CommRingCat.hom_id, RingHom.id_apply,
      Localization.localRingHom_mk']
    refine congrArg₂ (IsLocalization.mk' _) ?_ (Subtype.ext ?_)
    · change (P.diag.map (𝟙 i)).hom r = r
      rw [P.diag.map_id]
      rfl
    · change (P.diag.map (𝟙 i)).hom s = s
      rw [P.diag.map_id]
      rfl
  map_comp {i j k} f g := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun x ↦ ?_
    obtain ⟨⟨r, s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective
      (colimitPrime P p i).primeCompl x
    rw [CommRingCat.hom_ofHom, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
      CommRingCat.hom_ofHom, Localization.localRingHom_mk', RingHom.comp_apply,
      Localization.localRingHom_mk', Localization.localRingHom_mk']
    refine congrArg₂ (IsLocalization.mk' _) ?_ (Subtype.ext ?_)
    · change (P.diag.map (f ≫ g)).hom r = (P.diag.map g).hom ((P.diag.map f).hom r)
      rw [P.diag.map_comp]
      rfl
    · change (P.diag.map (f ≫ g)).hom s = (P.diag.map g).hom ((P.diag.map f).hom s)
      rw [P.diag.map_comp]
      rfl

/-- The cocone over `localizationDiag P p` with apex `Localization.AtPrime p`. -/
private noncomputable def localizationCocone : Cocone (localizationDiag P p) where
  pt := .of (Localization.AtPrime p)
  ι :=
    { app i := CommRingCat.ofHom <|
        Localization.localRingHom (colimitPrime P p i) p (P.ι.app i).hom.toRingHom rfl
      naturality {i j} f := by
        apply CommRingCat.hom_ext
        refine RingHom.ext fun (x : Localization.AtPrime (colimitPrime P p i)) ↦ ?_
        obtain ⟨⟨r, s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective
          (colimitPrime P p i).primeCompl x
        change (Localization.localRingHom (colimitPrime P p j) p (P.ι.app j).hom.toRingHom rfl)
            ((Localization.localRingHom (colimitPrime P p i) (colimitPrime P p j)
              (P.diag.map f).hom.toRingHom (colimitPrime_comap_diag P p f))
                (IsLocalization.mk' _ r ⟨s, hs⟩)) =
          (Localization.localRingHom (colimitPrime P p i) p (P.ι.app i).hom.toRingHom rfl)
            (IsLocalization.mk' _ r ⟨s, hs⟩)
        rw [Localization.localRingHom_mk', Localization.localRingHom_mk',
          Localization.localRingHom_mk']
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
    (ColimitPresentation.ι_app_diag_map_apply P (IsFiltered.leftToMax i₁ i₂) s₀).trans hs₀
  have hu' : (P.ι.app i).hom u' = u :=
    (ColimitPresentation.ι_app_diag_map_apply P (IsFiltered.rightToMax i₁ i₂) u₀).trans hu₀
  have hu'_mem : u' ∈ (colimitPrime P p i).primeCompl := fun hmem ↦ hu (hu' ▸ hmem)
  refine ⟨i, IsLocalization.mk' _ s' ⟨u', hu'_mem⟩, ?_⟩
  rw [Localization.localRingHom_mk']
  exact congrArg₂ (IsLocalization.mk' _) hs' (Subtype.ext hu')

/-- If two elements of `Localization.AtPrime (p.comap (algebraMap R S))` have equal images in
`Localization.AtPrime p`, they have equal images in `Localization.AtPrime (colimitPrime P p j)`
for some `j : ι`. -/
private lemma exists_localRingHom_eq_of_localRingHom_eq
    (x y : Localization.AtPrime (p.comap (algebraMap R S)))
    (hxy : Localization.localRingHom (p.comap (algebraMap R S)) p (algebraMap R S) rfl x =
        Localization.localRingHom (p.comap (algebraMap R S)) p (algebraMap R S) rfl y) :
    ∃ (j : ι),
      Localization.localRingHom (p.comap (algebraMap R S)) (colimitPrime P p j)
          (algebraMap R (P.diag.obj j)) (colimitPrime_comap_algebraMap P p j) x =
        Localization.localRingHom (p.comap (algebraMap R S)) (colimitPrime P p j)
          (algebraMap R (P.diag.obj j)) (colimitPrime_comap_algebraMap P p j) y := by
  obtain ⟨⟨r₁, s₁, hs₁⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (p.comap (algebraMap R S)).primeCompl x
  obtain ⟨⟨r₂, s₂, hs₂⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (p.comap (algebraMap R S)).primeCompl y
  rw [Localization.localRingHom_mk', Localization.localRingHom_mk'] at hxy
  obtain ⟨⟨c, hcp⟩, hc⟩ := (IsLocalization.eq (S := Localization.AtPrime p)).mp hxy
  obtain ⟨i₀, c', hc'⟩ := Concrete.isColimit_exists_rep _ P.isColimit c
  have hkey :
      (P.ι.app i₀).hom (c' * (algebraMap R (P.diag.obj i₀) s₂ *
          algebraMap R (P.diag.obj i₀) r₁)) =
      (P.ι.app i₀).hom (c' * (algebraMap R (P.diag.obj i₀) s₁ *
          algebraMap R (P.diag.obj i₀) r₂)) := by
    simp only [map_mul, (P.ι.app i₀).hom.commutes, hc']
    exact hc
  obtain ⟨j, fij, hjeq⟩ := (IsColimit.eq_iff' P.isColimit _ _).mp hkey
  refine ⟨j, ?_⟩
  let cj : P.diag.obj j := (P.diag.map fij).hom c'
  have hcj_to_c : (P.ι.app j).hom cj = c :=
    (ColimitPresentation.ι_app_diag_map_apply P fij c').trans hc'
  have hcj_mem : cj ∈ (colimitPrime P p j).primeCompl := fun hmem ↦ hcp (hcj_to_c ▸ hmem)
  have hq_eq_j : p.comap (algebraMap R S) =
      (colimitPrime P p j).comap (algebraMap R (P.diag.obj j)) :=
    colimitPrime_comap_algebraMap P p j
  have hs₁' : s₁ ∈ ((colimitPrime P p j).comap (algebraMap R (P.diag.obj j))).primeCompl :=
    fun hmem ↦ hs₁ (hq_eq_j.symm ▸ hmem)
  have hs₂' : s₂ ∈ ((colimitPrime P p j).comap (algebraMap R (P.diag.obj j))).primeCompl :=
    fun hmem ↦ hs₂ (hq_eq_j.symm ▸ hmem)
  rw [Localization.localRingHom_mk', Localization.localRingHom_mk', IsLocalization.eq]
  refine ⟨⟨cj, hcj_mem⟩, ?_⟩
  have hjeq' :
      (P.diag.map fij).hom
        (c' * (algebraMap R (P.diag.obj i₀) s₂ * algebraMap R (P.diag.obj i₀) r₁)) =
      (P.diag.map fij).hom
        (c' * (algebraMap R (P.diag.obj i₀) s₁ * algebraMap R (P.diag.obj i₀) r₂)) := hjeq
  simp only [map_mul, AlgHom.commutes] at hjeq'
  exact hjeq'

/-- If two elements of `Localization.AtPrime (colimitPrime P p i)` have equal images in
`Localization.AtPrime p`, they become equal in `Localization.AtPrime (colimitPrime P p k)` for
some morphism `i ⟶ k`. -/
private lemma exists_eq_of_localRingHomDiag_eq (i : ι)
    (x y : Localization.AtPrime (colimitPrime P p i))
    (hxy : (localizationCocone P p).ι.app i x = (localizationCocone P p).ι.app i y) :
    ∃ (k : ι) (f : i ⟶ k),
      (localizationDiag P p).map f x = (localizationDiag P p).map f y := by
  change Localization.localRingHom (colimitPrime P p i) p (P.ι.app i).hom.toRingHom rfl x =
    Localization.localRingHom (colimitPrime P p i) p (P.ι.app i).hom.toRingHom rfl y at hxy
  obtain ⟨⟨r₁, s₁, hs₁⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (colimitPrime P p i).primeCompl x
  obtain ⟨⟨r₂, s₂, hs₂⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (colimitPrime P p i).primeCompl y
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
    simp only [map_mul, ColimitPresentation.ι_app_diag_map_apply P li,
      ColimitPresentation.ι_app_diag_map_apply P rk, c'', hc']
    exact hc
  obtain ⟨k, fij, hjeq⟩ := (IsColimit.eq_iff' P.isColimit _ _).mp hkey
  refine ⟨k, li ≫ fij, ?_⟩
  let ck : P.diag.obj k := (P.diag.map fij).hom c''
  have hck_to_c : (P.ι.app k).hom ck = c := by
    change (P.ι.app k).hom ((P.diag.map fij).hom ((P.diag.map rk).hom c')) = c
    rw [ColimitPresentation.ι_app_diag_map_apply P fij,
      ColimitPresentation.ι_app_diag_map_apply P rk, hc']
  have hck_mem : ck ∈ (colimitPrime P p k).primeCompl := fun hmem ↦ hcp (hck_to_c ▸ hmem)
  have hcomp (z : P.diag.obj i) :
      (P.diag.map fij).hom ((P.diag.map li).hom z) = (P.diag.map (li ≫ fij)).hom z := by
    change ((P.diag.map fij).hom ∘ (P.diag.map li).hom) z = _
    rw [P.diag.map_comp]
    rfl
  change Localization.localRingHom (colimitPrime P p i) (colimitPrime P p k)
      (P.diag.map (li ≫ fij)).hom.toRingHom (colimitPrime_comap_diag P p (li ≫ fij))
      (IsLocalization.mk' _ r₁ ⟨s₁, hs₁⟩) =
    Localization.localRingHom (colimitPrime P p i) (colimitPrime P p k)
      (P.diag.map (li ≫ fij)).hom.toRingHom (colimitPrime_comap_diag P p (li ≫ fij))
      (IsLocalization.mk' _ r₂ ⟨s₂, hs₂⟩)
  rw [Localization.localRingHom_mk', Localization.localRingHom_mk', IsLocalization.eq]
  refine ⟨⟨ck, hck_mem⟩, ?_⟩
  have hjeq' :
      (P.diag.map fij).hom (c'' * ((P.diag.map li).hom s₂ * (P.diag.map li).hom r₁)) =
        (P.diag.map fij).hom (c'' * ((P.diag.map li).hom s₁ * (P.diag.map li).hom r₂)) := hjeq
  simp only [map_mul, hcomp] at hjeq'
  exact hjeq'

/-- The localization of a filtered colimit of `R`-algebras at a prime is the filtered colimit of
the localizations at the contracted primes. -/
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

/-- If `S` is a filtered colimit of `R`-algebras `Aᵢ` and each `R → Aᵢ` is bijective on stalks,
then so is `R → S`. -/
lemma of_colimitPresentation
    (h : ∀ i, Algebra.BijectiveOnStalks R (P.diag.obj i)) :
    Algebra.BijectiveOnStalks R S := by
  refine ⟨fun p hp ↦ ⟨?_, ?_⟩⟩
  · intro x y hxy
    obtain ⟨j, hxy_j⟩ := exists_localRingHom_eq_of_localRingHom_eq P p x y hxy
    exact ((RingHom.bijectiveOnStalks_algebraMap.mpr (h j)).localRingHom_of_eq
      (colimitPrime_comap_algebraMap P p j)).1 hxy_j
  · intro z
    obtain ⟨i, zᵢ, rfl⟩ := exists_localRingHom_eq P p z
    obtain ⟨w, rfl⟩ :=
      ((RingHom.bijectiveOnStalks_algebraMap.mpr (h i)).localRingHom_of_eq
        (colimitPrime_comap_algebraMap P p i)).2 zᵢ
    refine ⟨w, ?_⟩
    have hcomm (r : R) :
        (P.ι.app i).hom (algebraMap R (P.diag.obj i) r) = algebraMap R S r :=
      (P.ι.app i).hom.commutes r
    obtain ⟨⟨r, s, hs⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (p.comap (algebraMap R S)).primeCompl w
    rw [Localization.localRingHom_mk', Localization.localRingHom_mk',
      Localization.localRingHom_mk']
    exact congrArg₂ (IsLocalization.mk' _) (hcomm r).symm (Subtype.ext (hcomm s).symm)

end ColimitPresentation

end Algebra.BijectiveOnStalks
