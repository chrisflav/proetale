/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Proetale.Algebra.StalkIso
import Proetale.Mathlib.Algebra.Category.CommAlgCat.Limits

/-!
# Localization of a filtered colimit of algebras at a prime

Let `S = colim_i Aᵢ` be a filtered colimit of `R`-algebras and let `p` be a prime of `S`. Writing
`pᵢ` for the contraction of `p` to `Aᵢ`, the localizations `(Aᵢ)_{pᵢ}` form a filtered diagram
with colimit `S_p`. This is `Localization.AtPrime.isColimitLocalizationCocone`.

As an application we show in `Algebra.BijectiveOnStalks.of_colimitPresentation` that being
bijective on stalks is stable under filtered colimits.
-/

universe u

open CategoryTheory Limits

namespace Localization.AtPrime

section ColimitPresentation

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type u} [SmallCategory ι] (P : ColimitPresentation ι (CommAlgCat.of R S))

/-- The contraction of an ideal `p` of the colimit `S` to a constituent `P.diag.obj i`. -/
noncomputable def contractionIdeal (p : Ideal S) (i : ι) : Ideal (P.diag.obj i) :=
  p.comap (P.ι.app i).hom.toRingHom

instance contractionIdeal.isPrime (p : Ideal S) [p.IsPrime] (i : ι) :
    (contractionIdeal P p i).IsPrime :=
  Ideal.IsPrime.comap _

@[simp]
lemma contractionIdeal_comap_algebraMap (p : Ideal S) (i : ι) :
    (contractionIdeal P p i).comap (algebraMap R (P.diag.obj i)) = p.comap (algebraMap R S) := by
  symm
  ext r
  simp only [Ideal.mem_comap, contractionIdeal,
    ← ColimitPresentation.ι_app_algebraMap_apply P i r]
  rfl

@[simp]
lemma contractionIdeal_comap_diag (p : Ideal S) {i j : ι} (f : i ⟶ j) :
    (contractionIdeal P p j).comap (P.diag.map f).hom.toRingHom = contractionIdeal P p i := by
  symm
  ext r
  change (P.ι.app i).hom r ∈ p ↔ (P.ι.app j).hom ((P.diag.map f).hom r) ∈ p
  rw [ColimitPresentation.ι_app_diag_map_apply P f r]

variable (p : Ideal S) [p.IsPrime]

/-- The diagram of localizations `Localization.AtPrime (contractionIdeal P p i)` for `i : ι`, with
transition maps given by `Localization.localRingHom`. -/
noncomputable def localizationDiag : ι ⥤ CommRingCat.{u} where
  obj i := .of (Localization.AtPrime (contractionIdeal P p i))
  map {i j} f := CommRingCat.ofHom <| Localization.localRingHom _ _
    (P.diag.map f).hom.toRingHom (contractionIdeal_comap_diag P p f).symm
  map_id i := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun x ↦ ?_
    obtain ⟨⟨r, s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective
      (contractionIdeal P p i).primeCompl x
    rw [CommRingCat.hom_ofHom, CommRingCat.hom_id, RingHom.id_apply,
      Localization.localRingHom_mk']
    exact congrArg₂ (IsLocalization.mk' _) (P.diag_map_id_apply i r)
      (Subtype.ext (P.diag_map_id_apply i s))
  map_comp {i j k} f g := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun x ↦ ?_
    obtain ⟨⟨r, s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective
      (contractionIdeal P p i).primeCompl x
    rw [CommRingCat.hom_ofHom, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
      CommRingCat.hom_ofHom, Localization.localRingHom_mk', RingHom.comp_apply,
      Localization.localRingHom_mk', Localization.localRingHom_mk']
    exact congrArg₂ (IsLocalization.mk' _) (P.diag_map_comp_apply f g r)
      (Subtype.ext (P.diag_map_comp_apply f g s))

lemma localizationDiag_map_apply {i j : ι} (f : i ⟶ j)
    (x : Localization.AtPrime (contractionIdeal P p i)) :
    ((localizationDiag P p).map f).hom x =
      Localization.localRingHom _ _ (P.diag.map f).hom.toRingHom
        (contractionIdeal_comap_diag P p f).symm x :=
  rfl

/-- The cocone over `localizationDiag P p` with apex `Localization.AtPrime p`. -/
noncomputable def localizationCocone : Cocone (localizationDiag P p) where
  pt := .of (Localization.AtPrime p)
  ι :=
    { app i := CommRingCat.ofHom <|
        Localization.localRingHom (contractionIdeal P p i) p (P.ι.app i).hom.toRingHom rfl
      naturality {i j} f := by
        apply CommRingCat.hom_ext
        refine RingHom.ext fun (x : Localization.AtPrime (contractionIdeal P p i)) ↦ ?_
        obtain ⟨⟨r, s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective
          (contractionIdeal P p i).primeCompl x
        change (Localization.localRingHom (contractionIdeal P p j) p (P.ι.app j).hom.toRingHom rfl)
            ((Localization.localRingHom (contractionIdeal P p i) (contractionIdeal P p j)
              (P.diag.map f).hom.toRingHom (contractionIdeal_comap_diag P p f).symm)
                (IsLocalization.mk' _ r ⟨s, hs⟩)) =
          (Localization.localRingHom (contractionIdeal P p i) p (P.ι.app i).hom.toRingHom rfl)
            (IsLocalization.mk' _ r ⟨s, hs⟩)
        rw [Localization.localRingHom_mk', Localization.localRingHom_mk',
          Localization.localRingHom_mk']
        exact congrArg₂ (IsLocalization.mk' _)
          (ColimitPresentation.ι_app_diag_map_apply P f r)
          (Subtype.ext (ColimitPresentation.ι_app_diag_map_apply P f s)) }

lemma localizationCocone_ι_app_apply (i : ι) (x : Localization.AtPrime (contractionIdeal P p i)) :
    ((localizationCocone P p).ι.app i).hom x =
      Localization.localRingHom (contractionIdeal P p i) p (P.ι.app i).hom.toRingHom rfl x :=
  rfl

/-- The comparison map from the localization of `R` at the contraction of `p` to the localization
of `P.diag.obj i` at the contraction of `p` to `P.diag.obj i`. -/
noncomputable def toLocalizationDiag (i : ι) :
    Localization.AtPrime (p.comap (algebraMap R S)) →+*
      Localization.AtPrime (contractionIdeal P p i) :=
  Localization.localRingHom _ _ (algebraMap R (P.diag.obj i))
    (contractionIdeal_comap_algebraMap P p i).symm

@[simp]
lemma localizationDiag_map_toLocalizationDiag {i j : ι} (f : i ⟶ j)
    (x : Localization.AtPrime (p.comap (algebraMap R S))) :
    ((localizationDiag P p).map f).hom (toLocalizationDiag P p i x) =
      toLocalizationDiag P p j x := by
  have h : (Localization.localRingHom (contractionIdeal P p i) (contractionIdeal P p j)
      (P.diag.map f).hom.toRingHom (contractionIdeal_comap_diag P p f).symm).comp
        (toLocalizationDiag P p i) = toLocalizationDiag P p j :=
    (Localization.localRingHom_unique _ (contractionIdeal P p j) (algebraMap R (P.diag.obj j))
      (contractionIdeal_comap_algebraMap P p j).symm fun r ↦ by
        rw [RingHom.comp_apply, toLocalizationDiag, Localization.localRingHom_to_map,
          Localization.localRingHom_to_map]
        exact congrArg _ ((P.diag.map f).hom.commutes r)).symm
  exact congr($h x)

@[simp]
lemma localizationCocone_ι_app_toLocalizationDiag (i : ι)
    (x : Localization.AtPrime (p.comap (algebraMap R S))) :
    ((localizationCocone P p).ι.app i).hom (toLocalizationDiag P p i x) =
      Localization.localRingHom (p.comap (algebraMap R S)) p (algebraMap R S) rfl x := by
  have h : (Localization.localRingHom (contractionIdeal P p i) p
      (P.ι.app i).hom.toRingHom rfl).comp (toLocalizationDiag P p i) =
        Localization.localRingHom (p.comap (algebraMap R S)) p (algebraMap R S) rfl :=
    (Localization.localRingHom_unique _ p (algebraMap R S) rfl fun r ↦ by
      rw [RingHom.comp_apply, toLocalizationDiag, Localization.localRingHom_to_map,
        Localization.localRingHom_to_map]
      exact congrArg _ ((P.ι.app i).hom.commutes r)).symm
  exact congr($h x)

variable [IsFiltered ι]

/-- Every element of `Localization.AtPrime p` lifts to an element of
`Localization.AtPrime (contractionIdeal P p i)` for some `i : ι`. -/
lemma exists_localizationCocone_ι_app_eq (z : Localization.AtPrime p) :
    ∃ (i : ι) (zᵢ : Localization.AtPrime (contractionIdeal P p i)),
      ((localizationCocone P p).ι.app i).hom zᵢ = z := by
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
  have hu'_mem : u' ∈ (contractionIdeal P p i).primeCompl := fun hmem ↦ hu (hu' ▸ hmem)
  refine ⟨i, IsLocalization.mk' _ s' ⟨u', hu'_mem⟩, ?_⟩
  change Localization.localRingHom (contractionIdeal P p i) p (P.ι.app i).hom.toRingHom rfl
    (IsLocalization.mk' _ s' ⟨u', hu'_mem⟩) = _
  rw [Localization.localRingHom_mk']
  exact congrArg₂ (IsLocalization.mk' _) hs' (Subtype.ext hu')

/-- If two elements of `Localization.AtPrime (contractionIdeal P p i)` have equal images in
`Localization.AtPrime p`, they become equal in `Localization.AtPrime (contractionIdeal P p k)` for
some morphism `i ⟶ k`. -/
lemma exists_localizationDiag_map_eq (i : ι)
    (x y : Localization.AtPrime (contractionIdeal P p i))
    (hxy : ((localizationCocone P p).ι.app i).hom x = ((localizationCocone P p).ι.app i).hom y) :
    ∃ (k : ι) (f : i ⟶ k),
      ((localizationDiag P p).map f).hom x = ((localizationDiag P p).map f).hom y := by
  simp only [localizationCocone_ι_app_apply] at hxy
  obtain ⟨⟨r₁, s₁, hs₁⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (contractionIdeal P p i).primeCompl x
  obtain ⟨⟨r₂, s₂, hs₂⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (contractionIdeal P p i).primeCompl y
  rw [Localization.localRingHom_mk', Localization.localRingHom_mk'] at hxy
  obtain ⟨⟨c, hcp⟩, hc⟩ := (IsLocalization.eq (S := Localization.AtPrime p)).mp hxy
  obtain ⟨k₀, c₀, hc₀⟩ := Concrete.isColimit_exists_rep _ P.isColimit c
  let l : i ⟶ IsFiltered.max i k₀ := IsFiltered.leftToMax i k₀
  let c' : P.diag.obj (IsFiltered.max i k₀) := (P.diag.map (IsFiltered.rightToMax i k₀)).hom c₀
  have hkey :
      (P.ι.app _).hom (c' * ((P.diag.map l).hom s₂ * (P.diag.map l).hom r₁)) =
        (P.ι.app _).hom (c' * ((P.diag.map l).hom s₁ * (P.diag.map l).hom r₂)) := by
    simp only [map_mul, ColimitPresentation.ι_app_diag_map_apply, c', hc₀]
    exact hc
  obtain ⟨k, g, hkeq⟩ := (IsColimit.eq_iff' P.isColimit _ _).mp hkey
  have hck : (P.ι.app k).hom ((P.diag.map g).hom c') = c := by
    rw [ColimitPresentation.ι_app_diag_map_apply, ColimitPresentation.ι_app_diag_map_apply, hc₀]
  have hck_mem : (P.diag.map g).hom c' ∈ (contractionIdeal P p k).primeCompl :=
    fun hmem ↦ hcp (hck ▸ hmem)
  refine ⟨k, l ≫ g, ?_⟩
  change Localization.localRingHom (contractionIdeal P p i) (contractionIdeal P p k)
      (P.diag.map (l ≫ g)).hom.toRingHom (contractionIdeal_comap_diag P p (l ≫ g)).symm
      (IsLocalization.mk' _ r₁ ⟨s₁, hs₁⟩) =
    Localization.localRingHom (contractionIdeal P p i) (contractionIdeal P p k)
      (P.diag.map (l ≫ g)).hom.toRingHom (contractionIdeal_comap_diag P p (l ≫ g)).symm
      (IsLocalization.mk' _ r₂ ⟨s₂, hs₂⟩)
  rw [Localization.localRingHom_mk', Localization.localRingHom_mk', IsLocalization.eq]
  refine ⟨⟨(P.diag.map g).hom c', hck_mem⟩, ?_⟩
  have hkeq' : (P.diag.map g).hom (c' * ((P.diag.map l).hom s₂ * (P.diag.map l).hom r₁)) =
      (P.diag.map g).hom (c' * ((P.diag.map l).hom s₁ * (P.diag.map l).hom r₂)) := hkeq
  simpa only [map_mul, ← P.diag_map_comp_apply] using hkeq'

/-- The localization of a filtered colimit `S = colim_i Aᵢ` of `R`-algebras at a prime `p` is the
filtered colimit of the localizations of the `Aᵢ` at the contractions of `p`. -/
noncomputable def isColimitLocalizationCocone : IsColimit (localizationCocone P p) := by
  have : ReflectsColimit (localizationDiag P p) (forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  exact isColimitOfReflects (forget CommRingCat.{u}) <|
    Types.FilteredColimit.isColimitOf' _ _
      (fun z ↦ (exists_localizationCocone_ι_app_eq P p z).imp
        fun _ h ↦ h.imp fun _ hzᵢ ↦ hzᵢ.symm)
      (fun i x y hxy ↦ exists_localizationDiag_map_eq P p i x y hxy)

end ColimitPresentation

end Localization.AtPrime

namespace Algebra.BijectiveOnStalks

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type u} [SmallCategory ι] [IsFiltered ι]
  (P : ColimitPresentation ι (CommAlgCat.of R S))

open Localization.AtPrime

/-- If `S` is a filtered colimit of `R`-algebras `Aᵢ` and each `R → Aᵢ` is bijective on stalks,
then so is `R → S`. -/
lemma of_colimitPresentation (h : ∀ i, Algebra.BijectiveOnStalks R (P.diag.obj i)) :
    Algebra.BijectiveOnStalks R S := by
  refine ⟨fun p hp ↦ ?_⟩
  -- The comparison maps `R_{p ∩ R} → (Aᵢ)_{pᵢ}` are bijective by assumption.
  have hφ (i : ι) : Function.Bijective (toLocalizationDiag P p i) :=
    (RingHom.bijectiveOnStalks_algebraMap.mpr (h i)).localRingHom_of_eq
      (contractionIdeal_comap_algebraMap P p i).symm
  obtain ⟨i₀⟩ : Nonempty ι := IsFiltered.nonempty
  refine ⟨fun x y hxy ↦ ?_, fun z ↦ ?_⟩
  · -- Injectivity: `x` and `y` already agree in `(Aᵢ)_{pᵢ}` for some `i`.
    obtain ⟨k, f, hk⟩ := exists_localizationDiag_map_eq P p i₀
      (toLocalizationDiag P p i₀ x) (toLocalizationDiag P p i₀ y)
      ((localizationCocone_ι_app_toLocalizationDiag P p i₀ x).trans
        (hxy.trans (localizationCocone_ι_app_toLocalizationDiag P p i₀ y).symm))
    exact (hφ k).1 (by simpa using hk)
  · -- Surjectivity: lift `z` to some `(Aᵢ)_{pᵢ}` and use that the comparison map is onto.
    obtain ⟨i, zᵢ, rfl⟩ := exists_localizationCocone_ι_app_eq P p z
    obtain ⟨w, rfl⟩ := (hφ i).2 zᵢ
    exact ⟨w, (localizationCocone_ι_app_toLocalizationDiag P p i w).symm⟩

end Algebra.BijectiveOnStalks
