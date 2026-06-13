/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.Flat
import Proetale.Algebra.Etale
import Proetale.Algebra.FaithfullyFlat
import Proetale.Algebra.Ind
import Proetale.Algebra.StalkIso
import Proetale.Mathlib.Algebra.Algebra.Pi
import Proetale.Mathlib.Algebra.Category.CommAlgCat.Limits
import Proetale.Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Ind-Zariski algebras and ring homomorphisms

In this file we define ind-Zariski algebras.
-/
universe u

open CategoryTheory Limits

section ColimitPresentationHelpers

namespace CategoryTheory.Limits.ColimitPresentation

variable {R : Type u} [CommRing R] {X : CommAlgCat.{u} R}
variable {ι : Type u} [SmallCategory ι]

/-- For a colimit presentation in `CommAlgCat R`, the colimit injection at the target composed
with the diagram map equals the colimit injection at the source. -/
@[simp]
lemma ι_app_diag_map_apply (P : ColimitPresentation ι X) {i j : ι} (f : i ⟶ j) (x : P.diag.obj i) :
    (P.ι.app j).hom ((P.diag.map f).hom x) = (P.ι.app i).hom x :=
  DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (P.w f)) x

lemma diag_map_id_apply (P : ColimitPresentation ι X) (i : ι) (x : P.diag.obj i) :
    (P.diag.map (𝟙 i)).hom x = x :=
  DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (P.diag.map_id i)) x

lemma diag_map_comp_apply (P : ColimitPresentation ι X) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
    (x : P.diag.obj i) :
    (P.diag.map (f ≫ g)).hom x = (P.diag.map g).hom ((P.diag.map f).hom x) :=
  DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (P.diag.map_comp f g)) x

variable {S : Type u} [CommRing S] [Algebra R S] in
/-- For a colimit presentation of `S` as a colimit of `R`-algebras, the colimit injection at `i`
sends the image of `r : R` in the `i`-th object of the diagram to the image of `r` in `S`. -/
lemma ι_app_algebraMap_apply (P : ColimitPresentation ι (CommAlgCat.of R S)) (i : ι) (r : R) :
    (P.ι.app i).hom (algebraMap R (P.diag.obj i) r) = algebraMap R S r :=
  (P.ι.app i).hom.commutes r

end CategoryTheory.Limits.ColimitPresentation

namespace Localization.AtPrime

section ColimitPresentation

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type u} [SmallCategory ι]
  (P : ColimitPresentation ι (CommAlgCat.of R S))

/-- The contraction of an ideal `p` of the colimit `S` to a constituent `P.diag.obj i`. -/
noncomputable def contractionIdeal (p : Ideal S) (i : ι) : Ideal (P.diag.obj i) :=
  p.comap (P.ι.app i).hom.toRingHom

instance contractionIdeal.isPrime (p : Ideal S) [p.IsPrime] (i : ι) :
    (contractionIdeal P p i).IsPrime :=
  Ideal.IsPrime.comap _

@[simp]
lemma contractionIdeal_comap_algebraMap (p : Ideal S) (i : ι) :
    (contractionIdeal P p i).comap (algebraMap R (P.diag.obj i)) =
      p.comap (algebraMap R S) := by
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

variable [IsFiltered ι]

/-- Every element of `Localization.AtPrime p` lifts to an element of
`Localization.AtPrime (contractionIdeal P p i)` for some `i : ι`. -/
lemma exists_localRingHom_eq (z : Localization.AtPrime p) :
    ∃ (i : ι) (zᵢ : Localization.AtPrime (contractionIdeal P p i)),
      Localization.localRingHom (contractionIdeal P p i) p
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
  have hu'_mem : u' ∈ (contractionIdeal P p i).primeCompl := fun hmem ↦ hu (hu' ▸ hmem)
  refine ⟨i, IsLocalization.mk' _ s' ⟨u', hu'_mem⟩, ?_⟩
  rw [Localization.localRingHom_mk']
  exact congrArg₂ (IsLocalization.mk' _) hs' (Subtype.ext hu')

/-- If two elements of `Localization.AtPrime (p.comap (algebraMap R S))` have equal images in
`Localization.AtPrime p`, they have equal images in `Localization.AtPrime (contractionIdeal P p j)`
for some `j : ι`. -/
lemma exists_localRingHom_eq_of_localRingHom_eq
    (x y : Localization.AtPrime (p.comap (algebraMap R S)))
    (hxy : Localization.localRingHom (p.comap (algebraMap R S)) p (algebraMap R S) rfl x =
        Localization.localRingHom (p.comap (algebraMap R S)) p (algebraMap R S) rfl y) :
    ∃ (j : ι),
      Localization.localRingHom (p.comap (algebraMap R S)) (contractionIdeal P p j)
          (algebraMap R (P.diag.obj j)) (contractionIdeal_comap_algebraMap P p j).symm x =
        Localization.localRingHom (p.comap (algebraMap R S)) (contractionIdeal P p j)
          (algebraMap R (P.diag.obj j)) (contractionIdeal_comap_algebraMap P p j).symm y := by
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
  have hcj_mem : cj ∈ (contractionIdeal P p j).primeCompl := fun hmem ↦ hcp (hcj_to_c ▸ hmem)
  have hq_eq_j : p.comap (algebraMap R S) =
      (contractionIdeal P p j).comap (algebraMap R (P.diag.obj j)) :=
    (contractionIdeal_comap_algebraMap P p j).symm
  rw [Localization.localRingHom_mk', Localization.localRingHom_mk', IsLocalization.eq]
  refine ⟨⟨cj, hcj_mem⟩, ?_⟩
  have hjeq' :
      (P.diag.map fij).hom
        (c' * (algebraMap R (P.diag.obj i₀) s₂ * algebraMap R (P.diag.obj i₀) r₁)) =
      (P.diag.map fij).hom
        (c' * (algebraMap R (P.diag.obj i₀) s₁ * algebraMap R (P.diag.obj i₀) r₂)) := hjeq
  simpa only [map_mul, AlgHom.commutes] using hjeq'

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
  have hck_mem : ck ∈ (contractionIdeal P p k).primeCompl := fun hmem ↦ hcp (hck_to_c ▸ hmem)
  change Localization.localRingHom (contractionIdeal P p i) (contractionIdeal P p k)
      (P.diag.map (li ≫ fij)).hom.toRingHom (contractionIdeal_comap_diag P p (li ≫ fij)).symm
      (IsLocalization.mk' _ r₁ ⟨s₁, hs₁⟩) =
    Localization.localRingHom (contractionIdeal P p i) (contractionIdeal P p k)
      (P.diag.map (li ≫ fij)).hom.toRingHom (contractionIdeal_comap_diag P p (li ≫ fij)).symm
      (IsLocalization.mk' _ r₂ ⟨s₂, hs₂⟩)
  rw [Localization.localRingHom_mk', Localization.localRingHom_mk', IsLocalization.eq]
  refine ⟨⟨ck, hck_mem⟩, ?_⟩
  have hjeq' :
      (P.diag.map fij).hom (c'' * ((P.diag.map li).hom s₂ * (P.diag.map li).hom r₁)) =
        (P.diag.map fij).hom (c'' * ((P.diag.map li).hom s₁ * (P.diag.map li).hom r₂)) := hjeq
  simpa only [map_mul, ← P.diag_map_comp_apply] using hjeq'

end ColimitPresentation

end Localization.AtPrime

namespace Algebra.BijectiveOnStalks

section ColimitPresentation

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type u} [SmallCategory ι] [IsFiltered ι]
  (P : ColimitPresentation ι (CommAlgCat.of R S))

open Localization.AtPrime

/-- If `S` is a filtered colimit of `R`-algebras `Aᵢ` and each `R → Aᵢ` is bijective on stalks,
then so is `R → S`. -/
lemma of_colimitPresentation
    (h : ∀ i, Algebra.BijectiveOnStalks R (P.diag.obj i)) :
    Algebra.BijectiveOnStalks R S := by
  refine ⟨fun p hp ↦ ⟨?_, ?_⟩⟩
  · intro x y hxy
    obtain ⟨j, hxy_j⟩ := exists_localRingHom_eq_of_localRingHom_eq P p x y hxy
    exact ((RingHom.bijectiveOnStalks_algebraMap.mpr (h j)).localRingHom_of_eq
      (contractionIdeal_comap_algebraMap P p j).symm).1 hxy_j
  · intro z
    obtain ⟨i, zᵢ, rfl⟩ := exists_localRingHom_eq P p z
    obtain ⟨w, rfl⟩ :=
      ((RingHom.bijectiveOnStalks_algebraMap.mpr (h i)).localRingHom_of_eq
        (contractionIdeal_comap_algebraMap P p i).symm).2 zᵢ
    refine ⟨w, ?_⟩
    obtain ⟨⟨r, s, hs⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (p.comap (algebraMap R S)).primeCompl w
    rw [Localization.localRingHom_mk', Localization.localRingHom_mk',
      Localization.localRingHom_mk']
    exact congrArg₂ (IsLocalization.mk' _)
      (ColimitPresentation.ι_app_algebraMap_apply P i r).symm
      (Subtype.ext (ColimitPresentation.ι_app_algebraMap_apply P i s).symm)

end ColimitPresentation

end Algebra.BijectiveOnStalks

end ColimitPresentationHelpers

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]

section Algebra

variable [Algebra R S] [Algebra R T]

/-- The object property on commutative `R`-algebras of being a local isomorphism. -/
def CommAlgCat.isLocalIso : ObjectProperty (CommAlgCat.{u} R) :=
  fun S ↦ Algebra.IsLocalIso R S

/-- The object property on commutative `R`-algebras of being finitely presented. -/
def CommAlgCat.finitePresentation : ObjectProperty (CommAlgCat.{u} R) :=
  fun S ↦ RingHom.FinitePresentation (algebraMap R S)

lemma CommAlgCat.isLocalIso_eq : isLocalIso R = RingHom.toObjectProperty RingHom.IsLocalIso R := by
  ext S
  exact RingHom.isLocalIso_algebraMap.symm

instance : (CommAlgCat.isLocalIso R).IsClosedUnderIsomorphisms := by
  rw [CommAlgCat.isLocalIso_eq]
  exact RingHom.IsLocalIso.respectsIso.isClosedUnderIsomorphisms_toObjectProperty R

instance : (CommAlgCat.isLocalIso R).IsClosedUnderFiniteProducts :=
  .of_isClosedUnderLimitsOfShape_discrete fun ι ↦ by
    intro
    apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
    rintro X ⟨F, hF⟩
    let S : ι → CommAlgCat.{u} R := fun i ↦ F.obj ⟨i⟩
    let natIso : F ≅ Discrete.functor S := Discrete.natIso (fun i ↦ Iso.refl _)
    let isoPi : (CommAlgCat.piFan S).pt ≅ limit (Discrete.functor S) :=
      (limit.isoLimitCone ⟨CommAlgCat.piFan S, CommAlgCat.isLimitPiFan S⟩).symm
    let isoLim : limit (Discrete.functor S) ≅ limit F :=
      (HasLimit.isoOfNatIso natIso).symm
    apply (CommAlgCat.isLocalIso R).prop_of_iso (isoPi ≪≫ isoLim)
    have inst (i : ι) : Algebra.IsLocalIso R (S i) := hF ⟨i⟩
    exact Algebra.IsLocalIso.pi_of_finite R (fun i ↦ S i)

/-- Étaleness is local on the target: if `s` spans the unit ideal of `S` and every
`Localization.Away g` for `g ∈ s` is étale over `R`, then `S` is étale over `R`. -/
lemma Algebra.Etale.of_span_eq_top_target (s : Set S) (hs : Ideal.span s = ⊤)
    (h : ∀ g ∈ s, Algebra.Etale R (Localization.Away g)) : Algebra.Etale R S := by
  rw [← RingHom.etale_algebraMap]
  refine RingHom.Etale.ofLocalizationSpanTarget (algebraMap R S) s hs fun ⟨g, hg⟩ ↦ ?_
  have : Algebra.Etale R (Localization.Away g) := h g hg
  rw [← IsScalarTower.algebraMap_eq R S (Localization.Away g)]
  exact RingHom.etale_algebraMap.mpr inferInstance

/-- Local isomorphisms of `R`-algebras are étale. -/
lemma Algebra.IsLocalIso.etale [Algebra.IsLocalIso R S] : Algebra.Etale R S :=
  Algebra.Etale.of_span_eq_top_target R S _
    (Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top R S) fun g hg ↦ by
      obtain ⟨r, _⟩ := hg.exists_away
      exact Algebra.Etale.of_isLocalizationAway r

/-- A local isomorphism of `R`-algebras is finitely presented. -/
lemma Algebra.IsLocalIso.finitePresentation [Algebra.IsLocalIso R S] :
    Algebra.FinitePresentation R S := by
  have := Algebra.IsLocalIso.etale R S
  infer_instance

/-- Finitely presented `R`-algebras are finitely presentable objects in `CommAlgCat R`. -/
lemma CommAlgCat.finitePresentation_le_isFinitelyPresentable :
    CommAlgCat.finitePresentation R ≤
      ObjectProperty.isFinitelyPresentable.{u} (CommAlgCat.{u} R) := by
  intro S hS
  have hunder : IsFinitelyPresentable.{u} ((commAlgCatEquivUnder (.of R)).functor.obj S) :=
    CommRingCat.isFinitelyPresentable_under _ _ (by convert hS using 1)
  have : Fact (Cardinal.aleph0 : Cardinal.{u}).IsRegular := Cardinal.fact_isRegular_aleph0
  exact (isCardinalPresentable_iff_of_isEquivalence (X := S) (κ := .aleph0)
    (commAlgCatEquivUnder (.of R)).functor).mp hunder

/-- Local isomorphisms are finitely presentable in `CommAlgCat R`. -/
lemma CommAlgCat.isLocalIso_le_isFinitelyPresentable :
    CommAlgCat.isLocalIso R ≤
      ObjectProperty.isFinitelyPresentable.{u} (CommAlgCat.{u} R) := fun S hS ↦
  have : Algebra.IsLocalIso R S := hS
  have := Algebra.IsLocalIso.finitePresentation R S
  CommAlgCat.finitePresentation_le_isFinitelyPresentable R S
    (RingHom.finitePresentation_algebraMap.mpr ‹_›)

/-- An algebra is ind-Zariski if it can be written as the filtered colimit of locally isomorphic
algebras. -/
@[stacks 096N, mk_iff]
class Algebra.IndZariski (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  exists_colimitPresentation : ∃ (ι : Type u) (_ : SmallCategory ι) (_ : IsFiltered ι)
    (P : ColimitPresentation ι (CommAlgCat.of R S)),
    ∀ (i : ι), Algebra.IsLocalIso R (P.diag.obj i)

namespace Algebra.IndZariski

lemma iff_ind_isLocalIso :
    Algebra.IndZariski R S ↔ ObjectProperty.ind.{u} (CommAlgCat.isLocalIso R) (.of R S) :=
  Algebra.indZariski_iff R S

lemma of_equiv (e : S ≃ₐ[R] T) [IndZariski R S] : IndZariski R T := by
  rwa [iff_ind_isLocalIso, (CommAlgCat.isLocalIso R).ind.prop_iff_of_iso (CommAlgCat.isoMk e.symm),
    ← iff_ind_isLocalIso]

instance pi {ι : Type u} [_root_.Finite ι] (S : ι → Type u) [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)] [∀ i, Algebra.IndZariski R (S i)] : Algebra.IndZariski R (∀ i, S i) := by
  rw [iff_ind_isLocalIso]
  apply ObjectProperty.LimitOfShape.prop (J := Discrete ι)
  refine ⟨⟨Discrete.functor fun i ↦ .of R (S i),
      Discrete.natTrans fun i ↦ CommAlgCat.ofHom (Pi.evalAlgHom _ _ _), ?_⟩, ?_⟩
  · exact CommAlgCat.isLimitPiFan fun i ↦ .of R (S i)
  · intro j
    dsimp
    rw [← iff_ind_isLocalIso]
    infer_instance

/-- The product of two ind-Zariski algebras is ind-Zariski. -/
instance prod [Algebra.IndZariski R S] [Algebra.IndZariski R T] :
    Algebra.IndZariski R (S × T) := by
  let F : ULift.{u} (Fin 2) → Type u := fun | ⟨0⟩ => S | ⟨1⟩ => T
  letI : ∀ i, CommRing (F i) := fun | ⟨0⟩ => ‹_› | ⟨1⟩ => ‹_›
  letI : ∀ i, Algebra R (F i) := fun | ⟨0⟩ => ‹_› | ⟨1⟩ => ‹_›
  haveI : ∀ i, IndZariski R (F i) := fun | ⟨0⟩ => ‹_› | ⟨1⟩ => ‹_›
  have := pi R F
  let e : (∀ i, F i) ≃ₐ[R] S × T :=
    { toFun := fun f ↦ (f ⟨0⟩, f ⟨1⟩)
      invFun := fun p ↦ fun | ⟨0⟩ => p.1 | ⟨1⟩ => p.2
      left_inv := fun f ↦ by ext ⟨i⟩; fin_cases i <;> rfl
      right_inv := fun ⟨_, _⟩ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  exact Algebra.IndZariski.of_equiv (R := R) (S := ∀ i, F i) (T := S × T) e

instance function {ι : Type u} [_root_.Finite ι] (S : Type u) [CommRing S]
    [Algebra R S] [Algebra.IndZariski R S] : Algebra.IndZariski R (ι → S) :=
  pi R (fun _ ↦ S)

variable {R}

instance (priority := 100) of_isLocalIso [Algebra.IsLocalIso R S] : Algebra.IndZariski R S := by
  rw [iff_ind_isLocalIso]
  exact ObjectProperty.le_ind _ _ ‹_›

instance refl : Algebra.IndZariski R R :=
  Algebra.IndZariski.of_isLocalIso _

/-- The index category for the colimit presentation `M⁻¹R = colim_{m ∈ M} R[1/m]`:
a wrapper around the submonoid `M`, equipped with the divisibility preorder. -/
@[ext]
structure AwayIndex {R : Type u} [CommRing R] (M : Submonoid R) where
  /-- The underlying element of the submonoid. -/
  val : R
  /-- The element belongs to `M`. -/
  property : val ∈ M

namespace AwayIndex

variable {R : Type u} [CommRing R] {M : Submonoid R}

instance : Preorder (AwayIndex M) where
  le m m' := m.val ∣ m'.val
  le_refl _ := dvd_refl _
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂

instance : IsDirected (AwayIndex M) (· ≤ ·) :=
  ⟨fun m m' ↦ ⟨⟨m.val * m'.val, M.mul_mem m.2 m'.2⟩,
    ⟨m'.val, rfl⟩, ⟨m.val, mul_comm _ _⟩⟩⟩

instance : Nonempty (AwayIndex M) := ⟨⟨1, M.one_mem⟩⟩

end AwayIndex

/-- The transition map `Localization.Away m → Localization.Away m'` when `m ∣ m'`,
viewed as an `R`-algebra homomorphism. -/
noncomputable def awayDvdHom (R : Type u) [CommRing R] {m m' : R} (h : m ∣ m')
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [IsLocalization.Away m A] [IsLocalization.Away m' B] : A →ₐ[R] B where
  __ := IsLocalization.Away.lift (S := A) m
    (g := algebraMap R B) (IsLocalization.Away.isUnit_of_dvd m' h)
  commutes' _ := IsLocalization.Away.lift_eq _ _ _

/-- The diagram `m ↦ Localization.Away m` indexed by elements of a submonoid `M ⊆ R`. -/
noncomputable def awayDiag (R : Type u) [CommRing R] (M : Submonoid R) :
    AwayIndex M ⥤ CommAlgCat.{u} R where
  obj m := .of R (Localization.Away m.val)
  map {m m'} h := CommAlgCat.ofHom (awayDvdHom R (m := m.val) (m' := m'.val) h.le)
  map_id m := by
    refine CommAlgCat.hom_ext (AlgHom.coe_ringHom_injective ?_)
    refine IsLocalization.ringHom_ext (.powers m.val) ?_
    ext _
    simp [awayDvdHom, IsLocalization.Away.lift]
  map_comp {m _ _} _ _ := by
    refine CommAlgCat.hom_ext (AlgHom.coe_ringHom_injective ?_)
    refine IsLocalization.ringHom_ext (.powers m.val) ?_
    ext _
    simp [awayDvdHom, IsLocalization.Away.lift]

instance (R : Type u) [CommRing R] (M : Submonoid R) (m : AwayIndex M) :
    IsLocalization.Away m.val ((awayDiag R M).obj m : Type u) :=
  inferInstanceAs (IsLocalization.Away m.val (Localization.Away m.val))

instance (R : Type u) [CommRing R] (M : Submonoid R) (m : AwayIndex M) :
    Algebra.IsLocalIso R ((awayDiag R M).obj m : Type u) :=
  inferInstanceAs (Algebra.IsLocalIso R (Localization.Away m.val))

/-- The `R`-algebra homomorphism `Localization.Away m → S` induced by the universal property,
where `S` is a localization of `R` at a submonoid `M` containing `m`. -/
noncomputable def awayToLocalization (R : Type u) [CommRing R] (M : Submonoid R)
    (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S] (m : AwayIndex M) :
    Localization.Away m.val →ₐ[R] S where
  __ := IsLocalization.Away.lift (S := Localization.Away m.val) m.val
    (g := algebraMap R S) (IsLocalization.map_units S ⟨m.val, m.property⟩)
  commutes' _ := IsLocalization.Away.lift_eq _ _ _

/-- The cocone over `awayDiag R M` with apex `S` given by the maps `awayToLocalization`. -/
noncomputable def awayCocone (R : Type u) [CommRing R] (M : Submonoid R)
    (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S] :
    awayDiag R M ⟶ (Functor.const (AwayIndex M)).obj (CommAlgCat.of R S) where
  app m := CommAlgCat.ofHom (awayToLocalization R M S m)
  naturality {m m'} _ := by
    refine CommAlgCat.hom_ext ?_
    have : Subsingleton (((awayDiag R M).obj m : Type u) →ₐ[R]
        (((Functor.const (AwayIndex M)).obj (CommAlgCat.of R S)).obj m' : Type u)) :=
      IsLocalization.algHom_subsingleton (.powers m.val)
    exact Subsingleton.elim _ _

/-- A localization of `R` at a submonoid `M` is the filtered colimit of `R[1/m]`
over `m ∈ M`, in the category of `R`-algebras. -/
noncomputable def awayColimitPresentation (R : Type u) [CommRing R] (M : Submonoid R)
    (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S] :
    ColimitPresentation (AwayIndex M) (CommAlgCat.of R S) where
  diag := awayDiag R M
  ι := awayCocone R M S
  isColimit :=
    { desc c := CommAlgCat.ofHom <| IsLocalization.liftAlgHom (M := M)
        (f := Algebra.ofId R c.pt) fun y ↦ by
          have key : (c.ι.app ⟨y.val, y.2⟩).hom
              (algebraMap R (Localization.Away y.val) y.val) = algebraMap R c.pt y.val :=
            (c.ι.app ⟨y.val, y.2⟩).hom.commutes y.val
          rw [Algebra.ofId_apply, ← key]
          exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away y.val) y.val).map
            (c.ι.app ⟨y.val, y.2⟩).hom
      fac c m := by
        refine CommAlgCat.hom_ext ?_
        have : Subsingleton (((awayDiag R M).obj m : Type u) →ₐ[R] (c.pt : Type u)) :=
          IsLocalization.algHom_subsingleton (.powers m.val)
        exact Subsingleton.elim _ _
      uniq c _ _ := by
        refine CommAlgCat.hom_ext ?_
        have : Subsingleton (S →ₐ[R] (c.pt : Type u)) :=
          IsLocalization.algHom_subsingleton M
        exact Subsingleton.elim _ _ }

lemma of_isLocalization (M : Submonoid R) [IsLocalization M S] : Algebra.IndZariski R S := by
  rw [iff_ind_isLocalIso]
  exact ⟨AwayIndex M, inferInstance, inferInstance, awayColimitPresentation R M S,
    fun m ↦ inferInstanceAs (Algebra.IsLocalIso R (Localization.Away m.val))⟩

instance localization (M : Submonoid R) : Algebra.IndZariski R (Localization M) :=
  of_isLocalization _ M

variable (R)

instance (priority := 100) _root_.Module.Flat.of_indZariski [Algebra.IndZariski R S] :
    Module.Flat R S := by
  rw [Module.Flat.iff_ind_flat]
  obtain ⟨J, _, _, pres, h⟩ := (Algebra.IndZariski.iff_ind_isLocalIso R S).mp ‹_›
  refine ⟨J, inferInstance, inferInstance, pres, fun i ↦ ?_⟩
  rw [CommAlgCat.flat_iff]
  exact @Algebra.IsLocalIso.flat _ _ _ _ _ (h i)

@[stacks 096T]
theorem bijectiveOnStalks_algebraMap [Algebra.IndZariski R S] :
    (algebraMap R S).BijectiveOnStalks := by
  obtain ⟨ι, _, _, P, h⟩ := IndZariski.exists_colimitPresentation (R := R) (S := S)
  exact RingHom.bijectiveOnStalks_algebraMap.mpr
    (Algebra.BijectiveOnStalks.of_colimitPresentation P fun i ↦
      RingHom.bijectiveOnStalks_algebraMap.mp
        (RingHom.IsLocalIso.bijectiveOnStalks (RingHom.isLocalIso_algebraMap.mpr (h i))))

instance (priority := 100) bijectiveOnStalks [Algebra.IndZariski R S] :
    Algebra.BijectiveOnStalks R S :=
  RingHom.bijectiveOnStalks_algebraMap.mp (bijectiveOnStalks_algebraMap R S)

/-- If `S` is a filtered colimit of ind-Zariski `R`-algebras, then `S` is ind-Zariski. -/
theorem of_colimitPresentation {ι : Type u} [SmallCategory ι] [IsFiltered ι]
    (P : ColimitPresentation ι (CommAlgCat.of R S))
    (h : ∀ (i : ι), Algebra.IndZariski R (P.diag.obj i)) : Algebra.IndZariski R S := by
  rw [iff_ind_isLocalIso,
    ← ObjectProperty.ind_ind (CommAlgCat.isLocalIso_le_isFinitelyPresentable R)]
  exact ⟨ι, ‹_›, ‹_›, P, fun i ↦ (iff_ind_isLocalIso R _).mp (h i)⟩

end Algebra.IndZariski

end Algebra

section RingHom

/-- A ring hom is ind-Zariski if and only if it is an ind-Zariski algebra. -/
@[stacks 096N, algebraize Algebra.IndZariski]
def RingHom.IndZariski {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.IndZariski R S

namespace RingHom.IndZariski

lemma algebraMap_iff [Algebra R S] :
    (algebraMap R S).IndZariski ↔ Algebra.IndZariski R S:=
  toAlgebra_algebraMap (R := R) (S := S).symm ▸ Iff.rfl

variable {R S T}

lemma iff_ind_isLocalIso (f : R →+* S) :
    f.IndZariski ↔ MorphismProperty.ind.{u}
      (RingHom.toMorphismProperty RingHom.IsLocalIso) (CommRingCat.ofHom f) := by
  algebraize [f]
  rw [RingHom.IndZariski, Algebra.IndZariski.iff_ind_isLocalIso, ← f.algebraMap_toAlgebra,
    RingHom.IsLocalIso.respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty,
    CommAlgCat.isLocalIso_eq]

/-- A ring hom is ind-Zariski if and only if it can be written
as a colimit of local isomorphisms. -/
lemma iff_exists {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f.hom.IndZariski ↔
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{u})
      (t : (Functor.const J).obj R ⟶ D) (c : D ⟶ (Functor.const J).obj S)
      (_ : IsColimit (.mk _ c)), ∀ i, (t.app i).hom.IsLocalIso ∧ t.app i ≫ c.app i = f :=
  RingHom.IndZariski.iff_ind_isLocalIso _

lemma id : (RingHom.id R).IndZariski :=
  Algebra.IndZariski.refl

/-- Local isomorphisms are finitely presentable morphisms in `CommRingCat`. -/
lemma _root_.CommRingCat.isLocalIso_le_isFinitelyPresentable :
    RingHom.toMorphismProperty RingHom.IsLocalIso ≤
      MorphismProperty.isFinitelyPresentable.{u} CommRingCat.{u} := by
  intro X Y f hf
  apply CommRingCat.isFinitelyPresentable_hom
  have hf' : f.hom.IsLocalIso := hf
  algebraize [f.hom]
  have hloc : Algebra.IsLocalIso X Y := hf'
  have := Algebra.IsLocalIso.finitePresentation X Y
  rw [← f.hom.algebraMap_toAlgebra]
  exact RingHom.finitePresentation_algebraMap.mpr ‹_›

/-- Ind-Zariski is equivalent to ind-ind-Zariski. -/
lemma iff_ind_indZariski (f : R →+* S) :
    f.IndZariski ↔ MorphismProperty.ind.{u}
      (RingHom.toMorphismProperty RingHom.IndZariski) (CommRingCat.ofHom f) := by
  rw [iff_ind_isLocalIso]
  have heq : RingHom.toMorphismProperty RingHom.IndZariski =
      MorphismProperty.ind.{u} (RingHom.toMorphismProperty RingHom.IsLocalIso) := by
    ext X Y g
    exact iff_ind_isLocalIso g.hom
  rw [heq, MorphismProperty.ind_ind CommRingCat.isLocalIso_le_isFinitelyPresentable.{u}]

lemma respectsIso :
    RingHom.RespectsIso
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) ↦ f.IndZariski) := by
  rw [RingHom.toMorphismProperty_respectsIso_iff]
  have heq : RingHom.toMorphismProperty
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) ↦ f.IndZariski) =
      MorphismProperty.ind.{u} (RingHom.toMorphismProperty RingHom.IsLocalIso) := by
    ext X Y g
    exact iff_ind_isLocalIso g.hom
  rw [heq]
  haveI : (RingHom.toMorphismProperty RingHom.IsLocalIso).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.IsLocalIso.respectsIso
  infer_instance

section AwaySpread

/-! ### Spreading out local isomorphisms along filtered colimits

Let `S = colim_j D_j` be a filtered colimit of rings and `g : S ⟶ A` a local isomorphism.
Since `g` is étale, it descends to an étale morphism `f₀ : D_{j₀} ⟶ A₀` at a finite stage by
`PreIndSpreads` for étale morphisms. We show that at a later stage `j₁`, the pushout
`f₁ : D_{j₁} ⟶ D_{j₁} ⊗_{D_{j₀}} A₀` is a local isomorphism.

The key technical tool is that the localization of the colimit away from an element is the
filtered colimit of the localizations away from its images (`awaySystem` below). -/

/-- The canonical morphism on `Localization.Away` induced by a morphism of rings. -/
private noncomputable def awayLift {B C : CommRingCat.{u}} (φ : B ⟶ C) (b : B) (c : C)
    (h : φ.hom b = c) :
    CommRingCat.of (Localization.Away b) ⟶ CommRingCat.of (Localization.Away c) :=
  CommRingCat.ofHom <| IsLocalization.Away.lift (S := Localization.Away b) b
    (g := (algebraMap C (Localization.Away c)).comp φ.hom)
    (by rw [RingHom.comp_apply, h]; exact IsLocalization.Away.algebraMap_isUnit c)

private lemma awayLift_algebraMap {B C : CommRingCat.{u}} (φ : B ⟶ C) (b : B) (c : C)
    (h : φ.hom b = c) (x : B) :
    (awayLift φ b c h).hom (algebraMap B (Localization.Away b) x) =
      algebraMap C (Localization.Away c) (φ.hom x) :=
  IsLocalization.Away.lift_eq b
    (by rw [RingHom.comp_apply, h]; exact IsLocalization.Away.algebraMap_isUnit c) x

private lemma away_hom_ext {B X : CommRingCat.{u}} {b : B}
    {f g : CommRingCat.of (Localization.Away b) ⟶ X}
    (h : ∀ x : B, f.hom (algebraMap B (Localization.Away b) x) =
      g.hom (algebraMap B (Localization.Away b) x)) : f = g :=
  CommRingCat.hom_ext <| IsLocalization.ringHom_ext (Submonoid.powers b) (RingHom.ext h)

private lemma mem_powers_map {B C : CommRingCat.{u}} (φ : B ⟶ C) (b : B) (c : C)
    (h : φ.hom b = c) (y : Submonoid.powers b) : φ.hom y ∈ Submonoid.powers c := by
  obtain ⟨n, hn⟩ := y.2
  have hn' : b ^ n = (y : B) := hn
  exact ⟨n, show c ^ n = φ.hom y by rw [← h, ← map_pow, hn']⟩

private lemma awayLift_mk' {B C : CommRingCat.{u}} (φ : B ⟶ C) (b : B) (c : C)
    (h : φ.hom b = c) (x : B) (y : Submonoid.powers b) :
    (awayLift φ b c h).hom (IsLocalization.mk' (Localization.Away b) x y) =
      IsLocalization.mk' (Localization.Away c) (φ.hom x)
        (⟨φ.hom y, mem_powers_map φ b c h y⟩ : Submonoid.powers c) := by
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  have hpow : (algebraMap C (Localization.Away c))
      ((⟨φ.hom y, mem_powers_map φ b c h y⟩ : Submonoid.powers c) : C) =
      (awayLift φ b c h).hom (algebraMap B (Localization.Away b) y) :=
    (awayLift_algebraMap φ b c h y).symm
  rw [hpow, ← map_mul, IsLocalization.mk'_spec, awayLift_algebraMap]

variable {J : Type u} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{u}}

/-- The leg of a cocone, with codomain the cocone point. -/
private def coconeι (c : Cocone D) (j : J) : D.obj j ⟶ c.pt :=
  c.ι.app j

omit [IsFiltered J] in
private lemma coconeι_w (c : Cocone D) {j j' : J} (f : j ⟶ j') :
    D.map f ≫ coconeι c j' = coconeι c j :=
  c.w f

omit [IsFiltered J] in
private lemma coconeι_w_apply (c : Cocone D) {j j' : J} (f : j ⟶ j') (x : D.obj j) :
    (coconeι c j').hom ((D.map f).hom x) = (coconeι c j).hom x := by
  calc (coconeι c j').hom ((D.map f).hom x) = (D.map f ≫ coconeι c j').hom x := rfl
    _ = (coconeι c j).hom x := congrArg (fun q ↦ q.hom x) (coconeι_w c f)

private lemma coconeι_exists_rep (c : Cocone D) (hc : IsColimit c) (x : c.pt) :
    ∃ (j : J) (y : D.obj j), (coconeι c j).hom y = x := by
  obtain ⟨j, y, hy⟩ := Concrete.isColimit_exists_rep _ hc x
  exact ⟨j, y, hy⟩

/-- The image of `r : D.obj j₀` at a later stage `k`. -/
private def rAt (j₀ : J) (r : D.obj j₀) (k : Under j₀) : D.obj k.right :=
  (D.map k.hom).hom r

omit [IsFiltered J] in
private lemma rAt_map (j₀ : J) (r : D.obj j₀) {k l : Under j₀} (t : k ⟶ l) :
    (D.map t.right).hom (rAt j₀ r k) = rAt j₀ r l := by
  have h : k.hom ≫ t.right = l.hom := Under.w t
  calc (D.map t.right).hom (rAt j₀ r k) = (D.map k.hom ≫ D.map t.right).hom r := rfl
    _ = rAt j₀ r l := by rw [← D.map_comp, h]; rfl

omit [IsFiltered J] in
private lemma rAt_cocone {c : Cocone D} (j₀ : J) (r : D.obj j₀) (k : Under j₀) :
    (coconeι c k.right).hom (rAt j₀ r k) = (coconeι c j₀).hom r :=
  coconeι_w_apply c k.hom r

/-- The filtered system of localizations away from the images of `r`. -/
private noncomputable def awaySystem (j₀ : J) (r : D.obj j₀) : Under j₀ ⥤ CommRingCat.{u} where
  obj k := .of (Localization.Away (rAt j₀ r k))
  map {k l} t := awayLift (D.map t.right) _ _ (rAt_map j₀ r t)
  map_id k := away_hom_ext fun x ↦ by
    rw [awayLift_algebraMap, CommRingCat.hom_id, RingHom.id_apply]
    congr 1
    have h : (𝟙 k : k ⟶ k).right = 𝟙 k.right := rfl
    rw [h, D.map_id, CommRingCat.hom_id, RingHom.id_apply]
  map_comp {k l m} t u := away_hom_ext fun x ↦ by
    rw [awayLift_algebraMap]
    change _ = (awayLift (D.map u.right) _ _ (rAt_map j₀ r u)).hom
      ((awayLift (D.map t.right) _ _ (rAt_map j₀ r t)).hom
        (algebraMap (D.obj k.right) (Localization.Away (rAt j₀ r k)) x))
    rw [awayLift_algebraMap, awayLift_algebraMap]
    congr 1
    have h : (t ≫ u).right = t.right ≫ u.right := rfl
    rw [h, D.map_comp]
    rfl

omit [IsFiltered J] in
private lemma awaySystem_map (j₀ : J) (r : D.obj j₀) {k l : Under j₀} (t : k ⟶ l) :
    (awaySystem (D := D) j₀ r).map t = awayLift (D.map t.right) _ _ (rAt_map j₀ r t) :=
  rfl

/-- The cocone over `awaySystem` with apex the localization of the colimit. -/
private noncomputable def awaySystemCocone (c : Cocone D) (j₀ : J) (r : D.obj j₀) :
    Cocone (awaySystem (D := D) j₀ r) where
  pt := .of (Localization.Away ((coconeι c j₀).hom r))
  ι :=
    { app k := awayLift (coconeι c k.right) _ _ (rAt_cocone j₀ r k)
      naturality {k l} t := away_hom_ext fun x ↦ by
        change (awayLift (coconeι c l.right) _ _ (rAt_cocone j₀ r l)).hom
            ((awayLift (D.map t.right) _ _ (rAt_map j₀ r t)).hom
              (algebraMap (D.obj k.right) (Localization.Away (rAt j₀ r k)) x)) =
          (awayLift (coconeι c k.right) _ _ (rAt_cocone j₀ r k)).hom
            (algebraMap (D.obj k.right) (Localization.Away (rAt j₀ r k)) x)
        rw [awayLift_algebraMap, awayLift_algebraMap, awayLift_algebraMap]
        congr 1
        exact coconeι_w_apply c t.right x }

omit [IsFiltered J] in
private lemma awaySystemCocone_app (c : Cocone D) (j₀ : J) (r : D.obj j₀) (k : Under j₀) :
    (awaySystemCocone c j₀ r).ι.app k = awayLift (coconeι c k.right) _ _ (rAt_cocone j₀ r k) :=
  rfl

/-- Every element of the localization of the colimit lifts to a stage. -/
private lemma awaySystem_exists_rep {c : Cocone D} (hc : IsColimit c) (j₀ : J) (r : D.obj j₀)
    (z : Localization.Away ((coconeι c j₀).hom r)) :
    ∃ (k : Under j₀) (y : Localization.Away (rAt j₀ r k)),
      ((awaySystemCocone c j₀ r).ι.app k).hom y = z := by
  obtain ⟨x, ⟨dz, hdz⟩, hz⟩ :=
    IsLocalization.exists_mk'_eq (Submonoid.powers ((coconeι c j₀).hom r)) z
  obtain ⟨n, hn⟩ := hdz
  have hn' : ((coconeι c j₀).hom r) ^ n = dz := hn
  obtain ⟨j₁, x₁, hx₁⟩ := coconeι_exists_rep c hc x
  set k : Under j₀ := Under.mk (IsFiltered.leftToMax j₀ j₁) with hk
  let x' : (D.obj k.right : Type u) := (D.map (IsFiltered.rightToMax j₀ j₁)).hom x₁
  refine ⟨k, IsLocalization.mk' _ x'
    (⟨rAt j₀ r k ^ n, n, rfl⟩ : Submonoid.powers (rAt j₀ r k)), ?_⟩
  refine (awayLift_mk' (coconeι c k.right) _ _ (rAt_cocone j₀ r k) x' _).trans (Eq.trans ?_ hz)
  refine congrArg₂ (IsLocalization.mk' _) ?_ (Subtype.ext ?_)
  · calc (coconeι c k.right).hom x'
        = (coconeι c k.right).hom ((D.map (IsFiltered.rightToMax j₀ j₁)).hom x₁) := rfl
      _ = (coconeι c j₁).hom x₁ := coconeι_w_apply c (IsFiltered.rightToMax j₀ j₁) x₁
      _ = x := hx₁
  · change (coconeι c k.right).hom (rAt j₀ r k ^ n) = dz
    rw [map_pow, rAt_cocone j₀ r, hn']

/-- Two stage elements equal in the localization of the colimit become equal at a later stage. -/
private lemma awaySystem_exists_map_eq {c : Cocone D} (hc : IsColimit c) (j₀ : J)
    (r : D.obj j₀) (k : Under j₀) (x y : Localization.Away (rAt j₀ r k))
    (hxy : ((awaySystemCocone c j₀ r).ι.app k).hom x =
      ((awaySystemCocone c j₀ r).ι.app k).hom y) :
    ∃ (l : Under j₀) (t : k ⟶ l),
      ((awaySystem (D := D) j₀ r).map t).hom x = ((awaySystem (D := D) j₀ r).map t).hom y := by
  obtain ⟨a, da, hx⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (rAt j₀ r k)) x
  obtain ⟨b, db, hy⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (rAt j₀ r k)) y
  rw [← hx, ← hy] at hxy ⊢
  have h1 := awayLift_mk' (coconeι c k.right) _ _ (rAt_cocone j₀ r k) a da
  have h2 := awayLift_mk' (coconeι c k.right) _ _ (rAt_cocone j₀ r k) b db
  have key := (h1.symm.trans hxy).trans h2
  rw [IsLocalization.eq] at key
  obtain ⟨⟨cv, hcv⟩, hcp⟩ := key
  obtain ⟨p, hp⟩ := hcv
  have hp' : ((coconeι c j₀).hom r) ^ p = cv := hp
  subst hp'
  have hcp' : ((coconeι c j₀).hom r) ^ p * ((coconeι c k.right).hom db *
      (coconeι c k.right).hom a) = ((coconeι c j₀).hom r) ^ p *
      ((coconeι c k.right).hom da * (coconeι c k.right).hom b) := hcp
  have hkey : (coconeι c k.right).hom ((rAt j₀ r k) ^ p * ((db : D.obj k.right) * a)) =
      (coconeι c k.right).hom ((rAt j₀ r k) ^ p * ((da : D.obj k.right) * b)) := by
    rw [map_mul, map_mul, map_mul, map_mul, map_pow, rAt_cocone j₀ r k]
    exact hcp'
  obtain ⟨j₂, w, hw⟩ := (IsColimit.eq_iff' hc _ _).mp hkey
  refine ⟨Under.mk (k.hom ≫ w), Under.homMk w rfl, ?_⟩
  have hr : (D.map w).hom (rAt j₀ r k) = rAt j₀ r (Under.mk (k.hom ≫ w)) := by
    calc (D.map w).hom (rAt j₀ r k) = (D.map k.hom ≫ D.map w).hom r := rfl
      _ = rAt j₀ r (Under.mk (k.hom ≫ w)) := by rw [← D.map_comp]; rfl
  have h3 := awayLift_mk' (D.map w) (rAt j₀ r k) (rAt j₀ r (Under.mk (k.hom ≫ w))) hr a da
  have h4 := awayLift_mk' (D.map w) (rAt j₀ r k) (rAt j₀ r (Under.mk (k.hom ≫ w))) hr b db
  refine (h3.trans ?_).trans h4.symm
  rw [IsLocalization.eq]
  refine ⟨⟨(D.map w).hom (rAt j₀ r k) ^ p, p, by rw [← hr]⟩, ?_⟩
  have hw' : (D.map w).hom ((rAt j₀ r k) ^ p * ((db : D.obj k.right) * a)) =
      (D.map w).hom ((rAt j₀ r k) ^ p * ((da : D.obj k.right) * b)) := hw
  have hfinal : (D.map w).hom (rAt j₀ r k) ^ p *
      ((D.map w).hom db * (D.map w).hom a) =
    (D.map w).hom (rAt j₀ r k) ^ p * ((D.map w).hom da * (D.map w).hom b) := by
    simpa only [map_mul, map_pow] using hw'
  exact hfinal

/-- The localization of a filtered colimit away from an element is the filtered colimit of
the localizations away from the images of the element. -/
private noncomputable def isColimitAwaySystemCocone {c : Cocone D} (hc : IsColimit c) (j₀ : J)
    (r : D.obj j₀) : IsColimit (awaySystemCocone c j₀ r) := by
  have : ReflectsFilteredColimits (forget CommRingCat.{u}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  refine isColimitOfReflects (forget _)
    (Types.FilteredColimit.isColimitOf' (awaySystem (D := D) j₀ r ⋙ forget _)
      ((forget _).mapCocone (awaySystemCocone c j₀ r)) ?_ ?_)
  · intro z
    obtain ⟨k, y, hy⟩ := awaySystem_exists_rep hc j₀ r z
    exact ⟨k, y, hy.symm⟩
  · intro k x y hxy
    exact awaySystem_exists_map_eq hc j₀ r k x y hxy

end AwaySpread

section PushSpread

variable {J : Type u} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{u}}

/-- The system of pushouts of `f₀` along the transition maps of a filtered system. -/
private noncomputable def pushSystem (j₀ : J) {A₀ : CommRingCat.{u}} (f₀ : D.obj j₀ ⟶ A₀) :
    Under j₀ ⥤ CommRingCat.{u} :=
  (Under.post D ⋙ Under.pushout f₀) ⋙ Under.forget _

/-- The structure morphism at a stage of the pushout system. -/
private noncomputable def pushInl (j₀ : J) {A₀ : CommRingCat.{u}} (f₀ : D.obj j₀ ⟶ A₀)
    (k : Under j₀) : D.obj k.right ⟶ (pushSystem j₀ f₀).obj k :=
  pushout.inl (D.map k.hom) f₀

/-- The morphism from `A₀` at a stage of the pushout system. -/
private noncomputable def pushInr (j₀ : J) {A₀ : CommRingCat.{u}} (f₀ : D.obj j₀ ⟶ A₀)
    (k : Under j₀) : A₀ ⟶ (pushSystem j₀ f₀).obj k :=
  pushout.inr (D.map k.hom) f₀

omit [IsFiltered J] in
private lemma pushSquare (j₀ : J) {A₀ : CommRingCat.{u}} (f₀ : D.obj j₀ ⟶ A₀) (k : Under j₀) :
    IsPushout (D.map k.hom) f₀ (pushInl j₀ f₀ k) (pushInr j₀ f₀ k) :=
  IsPushout.of_hasPushout (D.map k.hom) f₀

omit [IsFiltered J] in
private lemma pushInl_map (j₀ : J) {A₀ : CommRingCat.{u}} (f₀ : D.obj j₀ ⟶ A₀)
    {k l : Under j₀} (t : k ⟶ l) :
    pushInl j₀ f₀ k ≫ (pushSystem j₀ f₀).map t = D.map t.right ≫ pushInl j₀ f₀ l := by
  dsimp [pushSystem, pushInl, Under.post, Under.pushout]
  exact pushout.inl_desc _ _ _

omit [IsFiltered J] in
private lemma pushInr_map (j₀ : J) {A₀ : CommRingCat.{u}} (f₀ : D.obj j₀ ⟶ A₀)
    {k l : Under j₀} (t : k ⟶ l) :
    pushInr j₀ f₀ k ≫ (pushSystem j₀ f₀).map t = pushInr j₀ f₀ l := by
  dsimp [pushSystem, pushInr, Under.post, Under.pushout]
  exact pushout.inr_desc _ _ _

variable {S A : CommRingCat.{u}} {s : D ⟶ (Functor.const J).obj S} {g : S ⟶ A}

/-- The cocone of the pushout system over `A`. -/
private noncomputable def pushCocone (_hs : IsColimit (Cocone.mk S s)) {j₀ : J}
    {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀} {v₀ : A₀ ⟶ A}
    (hpo : IsPushout (s.app j₀) f₀ g v₀) : Cocone (pushSystem j₀ f₀) :=
  ((Under.pushout f₀ ⋙ Under.forget _).mapCocone
    ((Cocone.mk _ s).underPost j₀)).extend hpo.isoPushout.inv

/-- The cocone of the pushout system is a colimit cocone. -/
private noncomputable def isColimitPushCocone (hs : IsColimit (Cocone.mk S s)) {j₀ : J}
    {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀} {v₀ : A₀ ⟶ A}
    (hpo : IsPushout (s.app j₀) f₀ g v₀) : IsColimit (pushCocone hs hpo) :=
  IsColimit.extendIso _ (isColimitOfPreserves _ (hs.underPost j₀))

omit [IsFiltered J] in
private lemma pushInl_cocone (hs : IsColimit (Cocone.mk S s)) {j₀ : J}
    {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀} {v₀ : A₀ ⟶ A}
    (hpo : IsPushout (s.app j₀) f₀ g v₀) (k : Under j₀) :
    pushInl j₀ f₀ k ≫ (pushCocone hs hpo).ι.app k = s.app k.right ≫ g := by
  have hkey : pushInl j₀ f₀ k ≫ ((Under.pushout f₀ ⋙ Under.forget _).mapCocone
      ((Cocone.mk _ s).underPost j₀)).ι.app k =
      s.app k.right ≫ pushout.inl (s.app j₀) f₀ := by
    dsimp [pushInl, Under.pushout, Cocone.underPost]
    exact pushout.inl_desc _ _ _
  have hcomp : pushInl j₀ f₀ k ≫ (pushCocone hs hpo).ι.app k =
      s.app k.right ≫ pushout.inl (s.app j₀) f₀ ≫ hpo.isoPushout.inv := by
    change pushInl j₀ f₀ k ≫ ((Under.pushout f₀ ⋙ Under.forget _).mapCocone
      ((Cocone.mk _ s).underPost j₀)).ι.app k ≫ hpo.isoPushout.inv = _
    exact congrArg (fun q ↦ q ≫ hpo.isoPushout.inv) hkey
  exact hcomp.trans (whisker_eq (s.app k.right) hpo.inl_isoPushout_inv)

omit [IsFiltered J] in
private lemma pushInr_cocone (hs : IsColimit (Cocone.mk S s)) {j₀ : J}
    {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀} {v₀ : A₀ ⟶ A}
    (hpo : IsPushout (s.app j₀) f₀ g v₀) (k : Under j₀) :
    pushInr j₀ f₀ k ≫ (pushCocone hs hpo).ι.app k = v₀ := by
  have hkey : pushInr j₀ f₀ k ≫ ((Under.pushout f₀ ⋙ Under.forget _).mapCocone
      ((Cocone.mk _ s).underPost j₀)).ι.app k =
      pushout.inr (s.app j₀) f₀ := by
    dsimp [pushInr, Under.pushout, Cocone.underPost]
    exact pushout.inr_desc _ _ _
  have hcomp : pushInr j₀ f₀ k ≫ (pushCocone hs hpo).ι.app k =
      pushout.inr (s.app j₀) f₀ ≫ hpo.isoPushout.inv := by
    change pushInr j₀ f₀ k ≫ ((Under.pushout f₀ ⋙ Under.forget _).mapCocone
      ((Cocone.mk _ s).underPost j₀)).ι.app k ≫ hpo.isoPushout.inv = _
    exact congrArg (fun q ↦ q ≫ hpo.isoPushout.inv) hkey
  exact hcomp.trans hpo.inr_isoPushout_inv

omit [IsFiltered J] in
/-- The pasted pushout square at a stage of the pushout system. -/
private lemma pushSquare_stage (hs : IsColimit (Cocone.mk S s)) {j₀ : J}
    {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀} {v₀ : A₀ ⟶ A}
    (hpo : IsPushout (s.app j₀) f₀ g v₀) (k : Under j₀) :
    IsPushout (s.app k.right) (pushInl j₀ f₀ k) g ((pushCocone hs hpo).ι.app k) := by
  have houter : IsPushout (D.map k.hom ≫ s.app k.right) f₀ g v₀ := by
    have hw : D.map k.hom ≫ s.app k.right = s.app j₀ := by
      have := s.naturality k.hom
      simp
    rw [hw]
    exact hpo
  have hdesc : (pushSquare j₀ f₀ k).desc (s.app k.right ≫ g) v₀
      (by rw [← Category.assoc, houter.w]) = (pushCocone hs hpo).ι.app k := by
    apply (pushSquare j₀ f₀ k).hom_ext
    · rw [IsPushout.inl_desc]
      exact (pushInl_cocone hs hpo k).symm
    · rw [IsPushout.inr_desc]
      exact (pushInr_cocone hs hpo k).symm
  rw [← hdesc]
  exact IsPushout.of_left' houter (pushSquare j₀ f₀ k)

end PushSpread

section AwayGood

/-! Pure ring-theoretic core of the spreading argument: given witnesses for invertibility and
surjectivity, the localization of `W` away from `ĝ` is the localization of `B` away from
`sel`. -/

variable {B W : Type u} [CommRing B] [CommRing W] (φ : B →+* W) (ĝ : W) (sel : B)

/-- `z` is a fraction over the image of `B` with denominator a power of `sel`. -/
private def AwayGood (z : Localization.Away ĝ) : Prop :=
  ∃ (x : B) (n : ℕ),
    z * algebraMap W (Localization.Away ĝ) (φ (sel ^ n)) =
      algebraMap W (Localization.Away ĝ) (φ x)

private lemma awayGood_mul {z₁ z₂ : Localization.Away ĝ} (h₁ : AwayGood φ ĝ sel z₁)
    (h₂ : AwayGood φ ĝ sel z₂) : AwayGood φ ĝ sel (z₁ * z₂) := by
  obtain ⟨x₁, n₁, e₁⟩ := h₁
  obtain ⟨x₂, n₂, e₂⟩ := h₂
  refine ⟨x₁ * x₂, n₁ + n₂, ?_⟩
  rw [pow_add, map_mul, map_mul, map_mul, map_mul]
  calc z₁ * z₂ * (algebraMap W (Localization.Away ĝ) (φ (sel ^ n₁)) *
        algebraMap W (Localization.Away ĝ) (φ (sel ^ n₂)))
      = (z₁ * algebraMap W (Localization.Away ĝ) (φ (sel ^ n₁))) *
          (z₂ * algebraMap W (Localization.Away ĝ) (φ (sel ^ n₂))) := by ring
    _ = algebraMap W (Localization.Away ĝ) (φ x₁) *
          algebraMap W (Localization.Away ĝ) (φ x₂) := by rw [e₁, e₂]

private lemma awayGood_add {z₁ z₂ : Localization.Away ĝ} (h₁ : AwayGood φ ĝ sel z₁)
    (h₂ : AwayGood φ ĝ sel z₂) : AwayGood φ ĝ sel (z₁ + z₂) := by
  obtain ⟨x₁, n₁, e₁⟩ := h₁
  obtain ⟨x₂, n₂, e₂⟩ := h₂
  refine ⟨x₁ * sel ^ n₂ + x₂ * sel ^ n₁, n₁ + n₂, ?_⟩
  simp only [pow_add, map_add, map_mul]
  calc (z₁ + z₂) * (algebraMap W (Localization.Away ĝ) (φ (sel ^ n₁)) *
        algebraMap W (Localization.Away ĝ) (φ (sel ^ n₂)))
      = (z₁ * algebraMap W (Localization.Away ĝ) (φ (sel ^ n₁))) *
          algebraMap W (Localization.Away ĝ) (φ (sel ^ n₂)) +
        (z₂ * algebraMap W (Localization.Away ĝ) (φ (sel ^ n₂))) *
          algebraMap W (Localization.Away ĝ) (φ (sel ^ n₁)) := by ring
    _ = _ := by rw [e₁, e₂]

private lemma awayGood_base (x : B) :
    AwayGood φ ĝ sel (algebraMap W (Localization.Away ĝ) (φ x)) :=
  ⟨x, 0, by simp⟩

private lemma awayGood_pow {z : Localization.Away ĝ} (h : AwayGood φ ĝ sel z) (N : ℕ) :
    AwayGood φ ĝ sel (z ^ N) := by
  induction N with
  | zero => exact ⟨1, 0, by simp⟩
  | succ n ih => rw [pow_succ]; exact awayGood_mul φ ĝ sel ih h

/-- The pure ring-theoretic verification: the witnesses imply that the localization of `W`
away from `ĝ` is the localization of `B` away from `sel`, via `φ`. -/
private theorem isLocalizationAway_of_witnesses
    (χ : W →+* Localization.Away sel) (hχφ : ∀ b, χ (φ b) = algebraMap B (Localization.Away sel) b)
    (u1y : W) (u1N u1M : ℕ) (hu1 : ĝ ^ u1M * (φ sel * u1y) = ĝ ^ (u1M + u1N))
    (u2z : Localization.Away sel) (hu2 : χ ĝ * u2z = 1)
    (he3 : ∃ (d' : B) (n' M' : ℕ), ĝ ^ M' * φ (sel ^ n') = ĝ ^ M' * (φ d' * ĝ))
    (hgood : ∀ w : W, AwayGood φ ĝ sel (algebraMap W (Localization.Away ĝ) w)) :
    letI : Algebra B (Localization.Away ĝ) :=
      ((algebraMap W (Localization.Away ĝ)).comp φ).toAlgebra
    IsLocalization.Away sel (Localization.Away ĝ) := by
  letI : Algebra B (Localization.Away ĝ) :=
    ((algebraMap W (Localization.Away ĝ)).comp φ).toAlgebra
  set L := Localization.Away ĝ
  have halg : ∀ b : B, algebraMap B L b = algebraMap W L (φ b) := fun _ ↦ rfl
  have hĝunit : IsUnit (algebraMap W L ĝ) := IsLocalization.Away.algebraMap_isUnit ĝ
  -- `sel` becomes invertible
  have hψs : IsUnit (algebraMap B L sel) := by
    have h1 := congrArg (algebraMap W L) hu1
    rw [map_mul, map_mul, map_pow, map_pow, pow_add] at h1
    have h2 : algebraMap W L (φ sel) * algebraMap W L u1y = algebraMap W L ĝ ^ u1N :=
      (hĝunit.pow u1M).mul_left_cancel h1
    rw [halg]
    exact isUnit_of_mul_isUnit_left (h2.symm ▸ hĝunit.pow u1N)
  -- the inverse map
  have hχunit : IsUnit (χ ĝ) := IsUnit.of_mul_eq_one _ hu2
  have hvloc : ∀ w : W,
      IsLocalization.Away.lift (S := L) ĝ (g := χ) hχunit (algebraMap W L w) = χ w :=
    fun w ↦ IsLocalization.Away.lift_eq ĝ hχunit w
  -- the inverse of `algebraMap W L ĝ` is good
  have hGoodInv : ∀ z : L, z * algebraMap W L ĝ = 1 → AwayGood φ ĝ sel z := by
    intro z hz
    obtain ⟨d', n', M', e3⟩ := he3
    refine ⟨d', n', ?_⟩
    have h1 := congrArg (algebraMap W L) e3
    rw [map_mul, map_mul, map_mul, map_pow] at h1
    have h2 : algebraMap W L (φ (sel ^ n')) =
        algebraMap W L (φ d') * algebraMap W L ĝ :=
      (hĝunit.pow M').mul_left_cancel h1
    calc z * algebraMap W L (φ (sel ^ n'))
        = z * (algebraMap W L (φ d') * algebraMap W L ĝ) := by rw [h2]
      _ = algebraMap W L (φ d') * (z * algebraMap W L ĝ) := by ring
      _ = algebraMap W L (φ d') := by rw [hz, mul_one]
  -- surjectivity
  have hsurj : ∀ z : L, ∃ x : B × (Submonoid.powers sel),
      z * algebraMap B L x.2 = algebraMap B L x.1 := by
    intro z
    obtain ⟨w, dy, hz⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers ĝ) z
    obtain ⟨N, hN⟩ := dy.2
    have hN' : ĝ ^ N = (dy : W) := hN
    have hzg : z * algebraMap W L ĝ ^ N = algebraMap W L w := by
      rw [← hz, ← map_pow, hN']
      exact IsLocalization.mk'_spec _ w dy
    obtain ⟨zinv, hzinv⟩ := hĝunit.exists_right_inv
    have hGoodzinv : AwayGood φ ĝ sel zinv :=
      hGoodInv zinv (by rw [mul_comm]; exact hzinv)
    have hzeq : z = algebraMap W L w * zinv ^ N := by
      have h1 : algebraMap W L ĝ ^ N * zinv ^ N = 1 := by
        rw [← mul_pow, hzinv, one_pow]
      calc z = z * (algebraMap W L ĝ ^ N * zinv ^ N) := by rw [h1, mul_one]
        _ = (z * algebraMap W L ĝ ^ N) * zinv ^ N := by ring
        _ = algebraMap W L w * zinv ^ N := by rw [hzg]
    obtain ⟨x, n, hx⟩ := awayGood_mul φ ĝ sel (hgood w) (awayGood_pow φ ĝ sel hGoodzinv N)
    refine ⟨⟨x, ⟨sel ^ n, n, rfl⟩⟩, ?_⟩
    rw [← hzeq] at hx
    exact hx
  -- the kernel condition
  have hker : ∀ x y : B, algebraMap B L x = algebraMap B L y →
      ∃ c : Submonoid.powers sel, (c : B) * x = (c : B) * y := by
    intro x y hxy
    have h2 := congrArg (IsLocalization.Away.lift (S := L) ĝ (g := χ) hχunit) hxy
    rw [halg, halg, hvloc, hvloc, hχφ, hχφ] at h2
    exact IsLocalization.exists_of_eq (M := Submonoid.powers sel) h2
  refine ⟨⟨?_, hsurj, fun {x y} h ↦ hker x y h⟩⟩
  rintro ⟨y, n, rfl⟩
  have : (algebraMap B L) ((fun x ↦ sel ^ x) n) = algebraMap B L sel ^ n := by
    change algebraMap B L (sel ^ n) = _
    rw [map_pow]
  rw [this]
  exact hψs.pow n

end AwayGood

section PieceSpread

variable {J : Type u} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{u}}

/-- The morphism from a stage pushout to the localization of the stage base induced by a
morphism `q` on `A₀`. -/
private noncomputable def pieceChi {j₀ : J} {A₀ : CommRingCat.{u}} (f₀ : D.obj j₀ ⟶ A₀)
    (k : Under j₀) (sel : D.obj k.right) (q : A₀ ⟶ CommRingCat.of (Localization.Away sel))
    (hq : f₀ ≫ q =
      D.map k.hom ≫ CommRingCat.ofHom (algebraMap (D.obj k.right) (Localization.Away sel))) :
    (pushSystem j₀ f₀).obj k ⟶ CommRingCat.of (Localization.Away sel) :=
  (pushSquare j₀ f₀ k).desc (CommRingCat.ofHom (algebraMap _ _)) q hq.symm

omit [IsFiltered J] in
private lemma pieceChi_inl {j₀ : J} {A₀ : CommRingCat.{u}} (f₀ : D.obj j₀ ⟶ A₀)
    (k : Under j₀) (sel : D.obj k.right) (q : A₀ ⟶ CommRingCat.of (Localization.Away sel))
    (hq : f₀ ≫ q =
      D.map k.hom ≫ CommRingCat.ofHom (algebraMap (D.obj k.right) (Localization.Away sel)))
    (b : D.obj k.right) :
    (pieceChi f₀ k sel q hq).hom ((pushInl j₀ f₀ k).hom b) =
      algebraMap (D.obj k.right) (Localization.Away sel) b := by
  have h := (pushSquare j₀ f₀ k).inl_desc (CommRingCat.ofHom
    (algebraMap (D.obj k.right) (Localization.Away sel))) q hq.symm
  exact congrArg (fun m ↦ m.hom b) h

omit [IsFiltered J] in
private lemma pieceChi_inr {j₀ : J} {A₀ : CommRingCat.{u}} (f₀ : D.obj j₀ ⟶ A₀)
    (k : Under j₀) (sel : D.obj k.right) (q : A₀ ⟶ CommRingCat.of (Localization.Away sel))
    (hq : f₀ ≫ q =
      D.map k.hom ≫ CommRingCat.ofHom (algebraMap (D.obj k.right) (Localization.Away sel)))
    (a : A₀) :
    (pieceChi f₀ k sel q hq).hom ((pushInr j₀ f₀ k).hom a) = q.hom a := by
  have h := (pushSquare j₀ f₀ k).inr_desc (CommRingCat.ofHom
    (algebraMap (D.obj k.right) (Localization.Away sel))) q hq.symm
  exact congrArg (fun m ↦ m.hom a) h

omit [IsFiltered J] in
private lemma pushSquare_w_apply {j₀ : J} {A₀ : CommRingCat.{u}} (f₀ : D.obj j₀ ⟶ A₀)
    (k : Under j₀) (r : D.obj j₀) :
    (pushInl j₀ f₀ k).hom ((D.map k.hom).hom r) = (pushInr j₀ f₀ k).hom (f₀.hom r) :=
  congrArg (fun m ↦ m.hom r) (pushSquare j₀ f₀ k).w

/-- All the data needed to verify that a stage of the pushout system is a standard open
immersion after localizing away from `ĝ`. -/
private structure PieceAt (j₀ : J) {A₀ : CommRingCat.{u}} (f₀ : D.obj j₀ ⟶ A₀)
    (gens : Finset A₀) (k : Under j₀) (ĝ : (pushSystem j₀ f₀).obj k) : Type u where
  /-- the element of the stage base ring -/
  selt : D.obj k.right
  /-- the descended morphism on `A₀` -/
  q : A₀ ⟶ CommRingCat.of (Localization.Away selt)
  hq : f₀ ≫ q =
    D.map k.hom ≫ CommRingCat.ofHom (algebraMap (D.obj k.right) (Localization.Away selt))
  /-- witness for invertibility of `selt` in the localization away from `ĝ` -/
  u1y : (pushSystem j₀ f₀).obj k
  u1N : ℕ
  u1M : ℕ
  hu1 : ĝ ^ u1M * ((pushInl j₀ f₀ k).hom selt * u1y) = ĝ ^ (u1M + u1N)
  /-- witness for invertibility of `χ ĝ` -/
  u2z : Localization.Away selt
  hu2 : (pieceChi f₀ k selt q hq).hom ĝ * u2z = 1
  he2 : ∀ a ∈ gens, ∃ (d : D.obj k.right) (n M : ℕ),
    ĝ ^ M * ((pushInr j₀ f₀ k).hom a * (pushInl j₀ f₀ k).hom selt ^ n) =
      ĝ ^ M * (pushInl j₀ f₀ k).hom d
  he3 : ∃ (d' : D.obj k.right) (n' M' : ℕ),
    ĝ ^ M' * (pushInl j₀ f₀ k).hom (selt ^ n') = ĝ ^ M' * ((pushInl j₀ f₀ k).hom d' * ĝ)

omit [IsFiltered J] in
/-- The stage-local verification: the piece data implies that the stage base maps to the
localization of the stage pushout away from `ĝ` by a standard open immersion. -/
private theorem PieceAt.isStandardOpenImmersion {j₀ : J} {A₀ : CommRingCat.{u}}
    {f₀ : D.obj j₀ ⟶ A₀} {gens : Finset A₀}
    (hgens : (letI := f₀.hom.toAlgebra
      Algebra.adjoin (D.obj j₀) (gens : Set A₀) = ⊤))
    {k : Under j₀} {ĝ : (pushSystem j₀ f₀).obj k} (P : PieceAt j₀ f₀ gens k ĝ) :
    ((algebraMap ((pushSystem j₀ f₀).obj k) (Localization.Away ĝ)).comp
      (pushInl j₀ f₀ k).hom).IsStandardOpenImmersion := by
  classical
  -- verify that every element of the localization is good
  have hgood : ∀ w : (pushSystem j₀ f₀).obj k,
      AwayGood (pushInl j₀ f₀ k).hom ĝ P.selt
        (algebraMap ((pushSystem j₀ f₀).obj k) (Localization.Away ĝ) w) := by
    have hĝunit : IsUnit (algebraMap ((pushSystem j₀ f₀).obj k) (Localization.Away ĝ) ĝ) :=
      IsLocalization.Away.algebraMap_isUnit ĝ
    -- generators of `A₀` are good
    have hGoodGen : ∀ a ∈ gens, AwayGood (pushInl j₀ f₀ k).hom ĝ P.selt
        (algebraMap _ (Localization.Away ĝ) ((pushInr j₀ f₀ k).hom a)) := by
      intro a ha
      obtain ⟨d, n, M, he2⟩ := P.he2 a ha
      refine ⟨d, n, ?_⟩
      have h1 := congrArg (algebraMap ((pushSystem j₀ f₀).obj k) (Localization.Away ĝ)) he2
      rw [map_mul, map_mul, map_mul, map_pow] at h1
      have h2 := (hĝunit.pow M).mul_left_cancel h1
      rw [← map_pow (pushInl j₀ f₀ k).hom] at h2
      exact h2
    -- all elements of `A₀` are good
    have hGoodA : ∀ a : A₀, AwayGood (pushInl j₀ f₀ k).hom ĝ P.selt
        (algebraMap _ (Localization.Away ĝ) ((pushInr j₀ f₀ k).hom a)) := by
      letI : Algebra (D.obj j₀) A₀ := f₀.hom.toAlgebra
      intro a
      have ha : a ∈ Algebra.adjoin (D.obj j₀) (gens : Set A₀) := hgens ▸ trivial
      induction ha using Algebra.adjoin_induction with
      | mem a ha => exact hGoodGen a ha
      | algebraMap r =>
          have heq : (pushInr j₀ f₀ k).hom (algebraMap (D.obj j₀) A₀ r) =
              (pushInl j₀ f₀ k).hom ((D.map k.hom).hom r) :=
            (pushSquare_w_apply f₀ k r).symm
          rw [heq]
          exact awayGood_base _ _ _ _
      | add a b _ _ hxa hxb =>
          rw [map_add, map_add]
          exact awayGood_add _ _ _ hxa hxb
      | mul a b _ _ hxa hxb =>
          rw [map_mul, map_mul]
          exact awayGood_mul _ _ _ hxa hxb
    -- transfer along the pushout structure
    letI : Algebra (D.obj j₀) (D.obj k.right) := (D.map k.hom).hom.toAlgebra
    letI : Algebra (D.obj j₀) A₀ := f₀.hom.toAlgebra
    letI : Algebra (D.obj k.right) ((pushSystem j₀ f₀).obj k) := (pushInl j₀ f₀ k).hom.toAlgebra
    letI : Algebra A₀ ((pushSystem j₀ f₀).obj k) := (pushInr j₀ f₀ k).hom.toAlgebra
    letI : Algebra (D.obj j₀) ((pushSystem j₀ f₀).obj k) :=
      ((pushInl j₀ f₀ k).hom.comp (D.map k.hom).hom).toAlgebra
    haveI : IsScalarTower (D.obj j₀) (D.obj k.right) ((pushSystem j₀ f₀).obj k) :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    haveI : IsScalarTower (D.obj j₀) A₀ ((pushSystem j₀ f₀).obj k) :=
      IsScalarTower.of_algebraMap_eq fun r ↦ pushSquare_w_apply f₀ k r
    have hpush : Algebra.IsPushout (D.obj j₀) (D.obj k.right) A₀ ((pushSystem j₀ f₀).obj k) := by
      rw [← CommRingCat.isPushout_iff_isPushout]
      exact pushSquare j₀ f₀ k
    intro w
    induction w using hpush.out.inductionOn with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul a => exact hGoodA a
    | smul b z hz =>
        rw [Algebra.smul_def, map_mul]
        exact awayGood_mul _ _ _ (awayGood_base _ _ _ b) hz
    | add z₁ z₂ h₁ h₂ =>
        rw [map_add]
        exact awayGood_add _ _ _ h₁ h₂
  -- assemble
  have hloc := isLocalizationAway_of_witnesses (pushInl j₀ f₀ k).hom ĝ P.selt
    (pieceChi f₀ k P.selt P.q P.hq).hom (pieceChi_inl f₀ k P.selt P.q P.hq)
    P.u1y P.u1N P.u1M P.hu1 P.u2z P.hu2 P.he3 hgood
  letI : Algebra (D.obj k.right) (Localization.Away ĝ) :=
    ((algebraMap ((pushSystem j₀ f₀).obj k) (Localization.Away ĝ)).comp
      (pushInl j₀ f₀ k).hom).toAlgebra
  exact ⟨⟨P.selt, hloc⟩⟩

omit [IsFiltered J] in
private lemma pushInl_map_apply (j₀ : J) {A₀ : CommRingCat.{u}} (f₀ : D.obj j₀ ⟶ A₀)
    {k l : Under j₀} (t : k ⟶ l) (b : D.obj k.right) :
    ((pushSystem j₀ f₀).map t).hom ((pushInl j₀ f₀ k).hom b) =
      (pushInl j₀ f₀ l).hom ((D.map t.right).hom b) := by
  calc ((pushSystem j₀ f₀).map t).hom ((pushInl j₀ f₀ k).hom b)
      = (pushInl j₀ f₀ k ≫ (pushSystem j₀ f₀).map t).hom b := rfl
    _ = (D.map t.right ≫ pushInl j₀ f₀ l).hom b := by rw [pushInl_map]
    _ = (pushInl j₀ f₀ l).hom ((D.map t.right).hom b) := rfl

omit [IsFiltered J] in
private lemma pushInr_map_apply (j₀ : J) {A₀ : CommRingCat.{u}} (f₀ : D.obj j₀ ⟶ A₀)
    {k l : Under j₀} (t : k ⟶ l) (a : A₀) :
    ((pushSystem j₀ f₀).map t).hom ((pushInr j₀ f₀ k).hom a) = (pushInr j₀ f₀ l).hom a := by
  calc ((pushSystem j₀ f₀).map t).hom ((pushInr j₀ f₀ k).hom a)
      = (pushInr j₀ f₀ k ≫ (pushSystem j₀ f₀).map t).hom a := rfl
    _ = (pushInr j₀ f₀ l).hom a := by rw [pushInr_map]

omit [IsFiltered J] in
private lemma pieceAt_push_hq {j₀ : J} {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀}
    {k : Under j₀} (selt : D.obj k.right) (q : A₀ ⟶ CommRingCat.of (Localization.Away selt))
    (hq : f₀ ≫ q =
      D.map k.hom ≫ CommRingCat.ofHom (algebraMap (D.obj k.right) (Localization.Away selt)))
    {l : Under j₀} (t : k ⟶ l) :
    f₀ ≫ q ≫ awayLift (D.map t.right) selt ((D.map t.right).hom selt) rfl =
      D.map l.hom ≫ CommRingCat.ofHom (algebraMap (D.obj l.right)
        (Localization.Away ((D.map t.right).hom selt))) := by
  refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
  have h1 : q.hom (f₀.hom r) =
      algebraMap (D.obj k.right) (Localization.Away selt) ((D.map k.hom).hom r) :=
    congrArg (fun m ↦ m.hom r) hq
  change (awayLift (D.map t.right) selt _ rfl).hom (q.hom (f₀.hom r)) =
    algebraMap (D.obj l.right) (Localization.Away ((D.map t.right).hom selt))
      ((D.map l.hom).hom r)
  rw [h1, awayLift_algebraMap]
  congr 1
  calc (D.map t.right).hom ((D.map k.hom).hom r) = (D.map k.hom ≫ D.map t.right).hom r := rfl
    _ = (D.map l.hom).hom r := by rw [← D.map_comp, Under.w t]

omit [IsFiltered J] in
private lemma pieceChi_push {j₀ : J} {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀}
    {k : Under j₀} (selt : D.obj k.right) (q : A₀ ⟶ CommRingCat.of (Localization.Away selt))
    (hq : f₀ ≫ q =
      D.map k.hom ≫ CommRingCat.ofHom (algebraMap (D.obj k.right) (Localization.Away selt)))
    {l : Under j₀} (t : k ⟶ l) :
    (pushSystem j₀ f₀).map t ≫ pieceChi f₀ l ((D.map t.right).hom selt)
        (q ≫ awayLift (D.map t.right) selt _ rfl) (pieceAt_push_hq selt q hq t) =
      pieceChi f₀ k selt q hq ≫ awayLift (D.map t.right) selt _ rfl := by
  apply (pushSquare j₀ f₀ k).hom_ext
  · refine CommRingCat.hom_ext (RingHom.ext fun b ↦ ?_)
    change (pieceChi f₀ l _ _ (pieceAt_push_hq selt q hq t)).hom
        (((pushSystem j₀ f₀).map t).hom ((pushInl j₀ f₀ k).hom b)) =
      (awayLift (D.map t.right) selt _ rfl).hom
        ((pieceChi f₀ k selt q hq).hom ((pushInl j₀ f₀ k).hom b))
    rw [pushInl_map_apply, pieceChi_inl, pieceChi_inl, awayLift_algebraMap]
  · refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
    change (pieceChi f₀ l _ _ (pieceAt_push_hq selt q hq t)).hom
        (((pushSystem j₀ f₀).map t).hom ((pushInr j₀ f₀ k).hom a)) =
      (awayLift (D.map t.right) selt _ rfl).hom
        ((pieceChi f₀ k selt q hq).hom ((pushInr j₀ f₀ k).hom a))
    rw [pushInr_map_apply, pieceChi_inr, pieceChi_inr]
    rfl

omit [IsFiltered J] in
private lemma pieceChi_push_apply {j₀ : J} {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀}
    {k : Under j₀} (selt : D.obj k.right) (q : A₀ ⟶ CommRingCat.of (Localization.Away selt))
    (hq : f₀ ≫ q =
      D.map k.hom ≫ CommRingCat.ofHom (algebraMap (D.obj k.right) (Localization.Away selt)))
    {l : Under j₀} (t : k ⟶ l) (w : (pushSystem j₀ f₀).obj k) :
    (pieceChi f₀ l ((D.map t.right).hom selt) (q ≫ awayLift (D.map t.right) selt _ rfl)
        (pieceAt_push_hq selt q hq t)).hom (((pushSystem j₀ f₀).map t).hom w) =
      (awayLift (D.map t.right) selt _ rfl).hom ((pieceChi f₀ k selt q hq).hom w) :=
  congrArg (fun m ↦ m.hom w) (pieceChi_push selt q hq t)

/-- Piece data pushes forward along stage maps. -/
private noncomputable def PieceAt.push {j₀ : J} {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀}
    {gens : Finset A₀} {k : Under j₀} {ĝ : (pushSystem j₀ f₀).obj k}
    (P : PieceAt j₀ f₀ gens k ĝ) {l : Under j₀} (t : k ⟶ l) :
    PieceAt j₀ f₀ gens l (((pushSystem j₀ f₀).map t).hom ĝ) where
  selt := (D.map t.right).hom P.selt
  q := P.q ≫ awayLift (D.map t.right) P.selt _ rfl
  hq := pieceAt_push_hq P.selt P.q P.hq t
  u1y := ((pushSystem j₀ f₀).map t).hom P.u1y
  u1N := P.u1N
  u1M := P.u1M
  hu1 := by
    have h := congrArg ((pushSystem j₀ f₀).map t).hom P.hu1
    rw [map_mul, map_mul, map_pow, map_pow, pushInl_map_apply] at h
    exact h
  u2z := (awayLift (D.map t.right) P.selt _ rfl).hom P.u2z
  hu2 := by
    rw [pieceChi_push_apply P.selt P.q P.hq t ĝ, ← map_mul, P.hu2, map_one]
  he2 := by
    intro a ha
    obtain ⟨d, n, M, h⟩ := P.he2 a ha
    refine ⟨(D.map t.right).hom d, n, M, ?_⟩
    have h1 := congrArg ((pushSystem j₀ f₀).map t).hom h
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, pushInl_map_apply, pushInl_map_apply,
      pushInr_map_apply] at h1
    exact h1
  he3 := by
    obtain ⟨d', n', M', h⟩ := P.he3
    refine ⟨(D.map t.right).hom d', n', M', ?_⟩
    have h1 := congrArg ((pushSystem j₀ f₀).map t).hom h
    rw [map_mul, map_mul, map_mul, map_pow, pushInl_map_apply, pushInl_map_apply,
      map_pow] at h1
    exact h1

section Descent

variable {S A : CommRingCat.{u}} {s : D ⟶ (Functor.const J).obj S} {g : S ⟶ A}

omit [IsFiltered J] in
private lemma pushCocone_w_apply (hs : IsColimit (Cocone.mk S s)) {j₀ : J}
    {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀} {v₀ : A₀ ⟶ A}
    (hpo : IsPushout (s.app j₀) f₀ g v₀) {k l : Under j₀} (t : k ⟶ l)
    (x : (pushSystem j₀ f₀).obj k) :
    ((pushCocone hs hpo).ι.app l).hom (((pushSystem j₀ f₀).map t).hom x) =
      ((pushCocone hs hpo).ι.app k).hom x := by
  calc ((pushCocone hs hpo).ι.app l).hom (((pushSystem j₀ f₀).map t).hom x)
      = ((pushSystem j₀ f₀).map t ≫ (pushCocone hs hpo).ι.app l).hom x := rfl
    _ = ((pushCocone hs hpo).ι.app k).hom x :=
        congrArg (fun m ↦ m.hom x) ((pushCocone hs hpo).w t)

omit [IsFiltered J] in
private lemma pushInl_cocone_apply (hs : IsColimit (Cocone.mk S s)) {j₀ : J}
    {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀} {v₀ : A₀ ⟶ A}
    (hpo : IsPushout (s.app j₀) f₀ g v₀) (k : Under j₀) (b : D.obj k.right) :
    ((pushCocone hs hpo).ι.app k).hom ((pushInl j₀ f₀ k).hom b) =
      g.hom ((coconeι (Cocone.mk S s) k.right).hom b) := by
  calc ((pushCocone hs hpo).ι.app k).hom ((pushInl j₀ f₀ k).hom b)
      = (pushInl j₀ f₀ k ≫ (pushCocone hs hpo).ι.app k).hom b := rfl
    _ = (s.app k.right ≫ g).hom b := congrArg (fun m ↦ m.hom b) (pushInl_cocone hs hpo k)
    _ = g.hom ((coconeι (Cocone.mk S s) k.right).hom b) := rfl

omit [IsFiltered J] in
private lemma pushInr_cocone_apply (hs : IsColimit (Cocone.mk S s)) {j₀ : J}
    {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀} {v₀ : A₀ ⟶ A}
    (hpo : IsPushout (s.app j₀) f₀ g v₀) (k : Under j₀) (a : A₀) :
    ((pushCocone hs hpo).ι.app k).hom ((pushInr j₀ f₀ k).hom a) = v₀.hom a := by
  calc ((pushCocone hs hpo).ι.app k).hom ((pushInr j₀ f₀ k).hom a)
      = (pushInr j₀ f₀ k ≫ (pushCocone hs hpo).ι.app k).hom a := rfl
    _ = v₀.hom a := congrArg (fun m ↦ m.hom a) (pushInr_cocone hs hpo k)

/-- The witness condition for a single generator. -/
private def E2C (j₀ : J) {A₀ : CommRingCat.{u}} (f₀ : D.obj j₀ ⟶ A₀) (k : Under j₀)
    (ĝk : (pushSystem j₀ f₀).obj k) (selk : D.obj k.right) (a : A₀) : Prop :=
  ∃ (d : D.obj k.right) (n M : ℕ),
    ĝk ^ M * ((pushInr j₀ f₀ k).hom a * (pushInl j₀ f₀ k).hom selk ^ n) =
      ĝk ^ M * (pushInl j₀ f₀ k).hom d

omit [IsFiltered J] in
private lemma E2C.push {j₀ : J} {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀} {k : Under j₀}
    {ĝk : (pushSystem j₀ f₀).obj k} {selk : D.obj k.right} {a : A₀}
    (h : E2C j₀ f₀ k ĝk selk a) {l : Under j₀} (t : k ⟶ l) :
    E2C j₀ f₀ l (((pushSystem j₀ f₀).map t).hom ĝk) ((D.map t.right).hom selk) a := by
  obtain ⟨d, n, M, hd⟩ := h
  refine ⟨(D.map t.right).hom d, n, M, ?_⟩
  have h1 := congrArg ((pushSystem j₀ f₀).map t).hom hd
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, pushInl_map_apply, pushInl_map_apply,
    pushInr_map_apply] at h1
  exact h1

/-- Descend the surjectivity witness for a single element of `A₀`. -/
private lemma exists_e2c (hs : IsColimit (Cocone.mk S s)) {j₀ : J}
    {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀} {v₀ : A₀ ⟶ A}
    (hpo : IsPushout (s.app j₀) f₀ g v₀)
    {k : Under j₀} (ĝk : (pushSystem j₀ f₀).obj k) (selk : D.obj k.right) (a : A₀)
    (sS : S) (hsel : (coconeι (Cocone.mk S s) k.right).hom selk = sS)
    (gA : A) (hĝ : ((pushCocone hs hpo).ι.app k).hom ĝk = gA)
    (hloc : (letI : Algebra S A := g.hom.toAlgebra
      IsLocalization.Away sS (Localization.Away gA))) :
    ∃ (l : Under j₀) (t : k ⟶ l),
      E2C j₀ f₀ l (((pushSystem j₀ f₀).map t).hom ĝk) ((D.map t.right).hom selk) a := by
  letI : Algebra S A := g.hom.toAlgebra
  haveI := hloc
  -- the image of `a` in the localization is a fraction over `S`
  obtain ⟨⟨dS, dsel⟩, hsurj⟩ := IsLocalization.surj (M := Submonoid.powers sS)
    (S := Localization.Away gA) (algebraMap A (Localization.Away gA) (v₀.hom a))
  obtain ⟨n, hn⟩ := dsel.2
  have hn' : sS ^ n = (dsel : S) := hn
  -- translate into an equation in `A`
  have hA : algebraMap A (Localization.Away gA) (v₀.hom a * g.hom (sS ^ n)) =
      algebraMap A (Localization.Away gA) (g.hom dS) := by
    rw [map_mul]
    have h1 : algebraMap A (Localization.Away gA) (g.hom (sS ^ n)) =
        algebraMap S (Localization.Away gA) ((dsel : S)) := by
      rw [IsScalarTower.algebraMap_apply S A (Localization.Away gA), hn']
      rfl
    have h2 : algebraMap A (Localization.Away gA) (g.hom dS) =
        algebraMap S (Localization.Away gA) dS := by
      rw [IsScalarTower.algebraMap_apply S A (Localization.Away gA)]
      rfl
    rw [h1, h2, ← hsurj]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers gA)
    (Localization.Away gA)).mp hA
  obtain ⟨M, hM⟩ := c.2
  have hM' : gA ^ M = (c : A) := hM
  rw [← hM'] at hc
  -- find a stage representative for `dS`
  obtain ⟨j₁, d₁, hd₁⟩ := coconeι_exists_rep (Cocone.mk S s) hs dS
  -- merge stages
  set l₁ : Under j₀ := Under.mk (k.hom ≫ IsFiltered.leftToMax k.right j₁) with hl₁
  set t₁ : k ⟶ l₁ := Under.homMk (IsFiltered.leftToMax k.right j₁) rfl with ht₁
  set d₂ : D.obj l₁.right := (D.map (IsFiltered.rightToMax k.right j₁)).hom d₁ with hd₂
  have hd₂S : (coconeι (Cocone.mk S s) l₁.right).hom d₂ = dS :=
    (coconeι_w_apply (Cocone.mk S s) (IsFiltered.rightToMax k.right j₁) d₁).trans hd₁
  set ĝ₁ := ((pushSystem j₀ f₀).map t₁).hom ĝk with hĝ₁
  set sel₁ := (D.map t₁.right).hom selk with hsel₁
  have hsel₁S : (coconeι (Cocone.mk S s) l₁.right).hom sel₁ = sS :=
    (coconeι_w_apply (Cocone.mk S s) t₁.right selk).trans hsel
  have hĝ₁A : ((pushCocone hs hpo).ι.app l₁).hom ĝ₁ = gA :=
    (pushCocone_w_apply hs hpo t₁ ĝk).trans hĝ
  -- the two sides of the equation at the stage
  set lhs : (pushSystem j₀ f₀).obj l₁ :=
    ĝ₁ ^ M * ((pushInr j₀ f₀ l₁).hom a * (pushInl j₀ f₀ l₁).hom sel₁ ^ n) with hlhs
  set rhs : (pushSystem j₀ f₀).obj l₁ :=
    ĝ₁ ^ M * (pushInl j₀ f₀ l₁).hom d₂ with hrhs
  have heq : ((pushCocone hs hpo).ι.app l₁).hom lhs = ((pushCocone hs hpo).ι.app l₁).hom rhs := by
    rw [hlhs, hrhs, map_mul, map_mul, map_mul, map_pow, map_pow, hĝ₁A,
      pushInr_cocone_apply, pushInl_cocone_apply, pushInl_cocone_apply, hsel₁S, hd₂S]
    calc gA ^ M * (v₀.hom a * g.hom sS ^ n)
        = gA ^ M * (v₀.hom a * g.hom (sS ^ n)) := by rw [map_pow]
      _ = gA ^ M * g.hom dS := hc
  obtain ⟨l₂, t₂, ht₂eq⟩ := (IsColimit.eq_iff' (isColimitPushCocone hs hpo) _ _).mp heq
  refine ⟨l₂, t₁ ≫ t₂, ?_⟩
  refine ⟨(D.map t₂.right).hom d₂, n, M, ?_⟩
  have h1 := ht₂eq
  rw [hlhs, hrhs, map_mul, map_mul, map_mul, map_pow, map_pow, pushInl_map_apply,
    pushInl_map_apply, pushInr_map_apply] at h1
  have hcompg : ((pushSystem j₀ f₀).map (t₁ ≫ t₂)).hom ĝk =
      ((pushSystem j₀ f₀).map t₂).hom ĝ₁ := by
    rw [Functor.map_comp]
    rfl
  have hcomps : (D.map (t₁ ≫ t₂).right).hom selk = (D.map t₂.right).hom sel₁ := by
    have h : (t₁ ≫ t₂).right = t₁.right ≫ t₂.right := rfl
    rw [h, D.map_comp]
    rfl
  rw [hcompg, hcomps]
  exact h1

/-- The witness condition for invertibility of the base element. -/
private def U1C (j₀ : J) {A₀ : CommRingCat.{u}} (f₀ : D.obj j₀ ⟶ A₀) (k : Under j₀)
    (ĝk : (pushSystem j₀ f₀).obj k) (selk : D.obj k.right) : Prop :=
  ∃ (y : (pushSystem j₀ f₀).obj k) (N M : ℕ),
    ĝk ^ M * ((pushInl j₀ f₀ k).hom selk * y) = ĝk ^ (M + N)

omit [IsFiltered J] in
private lemma U1C.push {j₀ : J} {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀} {k : Under j₀}
    {ĝk : (pushSystem j₀ f₀).obj k} {selk : D.obj k.right}
    (h : U1C j₀ f₀ k ĝk selk) {l : Under j₀} (t : k ⟶ l) :
    U1C j₀ f₀ l (((pushSystem j₀ f₀).map t).hom ĝk) ((D.map t.right).hom selk) := by
  obtain ⟨y, N, M, hy⟩ := h
  refine ⟨((pushSystem j₀ f₀).map t).hom y, N, M, ?_⟩
  have h1 := congrArg ((pushSystem j₀ f₀).map t).hom hy
  rw [map_mul, map_mul, map_pow, map_pow, pushInl_map_apply] at h1
  exact h1

/-- The witness condition for the inverse of `ĝ`. -/
private def E3C (j₀ : J) {A₀ : CommRingCat.{u}} (f₀ : D.obj j₀ ⟶ A₀) (k : Under j₀)
    (ĝk : (pushSystem j₀ f₀).obj k) (selk : D.obj k.right) : Prop :=
  ∃ (d' : D.obj k.right) (n' M' : ℕ),
    ĝk ^ M' * (pushInl j₀ f₀ k).hom (selk ^ n') = ĝk ^ M' * ((pushInl j₀ f₀ k).hom d' * ĝk)

omit [IsFiltered J] in
private lemma E3C.push {j₀ : J} {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀} {k : Under j₀}
    {ĝk : (pushSystem j₀ f₀).obj k} {selk : D.obj k.right}
    (h : E3C j₀ f₀ k ĝk selk) {l : Under j₀} (t : k ⟶ l) :
    E3C j₀ f₀ l (((pushSystem j₀ f₀).map t).hom ĝk) ((D.map t.right).hom selk) := by
  obtain ⟨d', n', M', hd⟩ := h
  refine ⟨(D.map t.right).hom d', n', M', ?_⟩
  have h1 := congrArg ((pushSystem j₀ f₀).map t).hom hd
  rw [map_mul, map_mul, map_mul, map_pow, pushInl_map_apply, pushInl_map_apply,
    map_pow] at h1
  exact h1

/-- Descend the invertibility witness for the base element. -/
private lemma exists_u1c (hs : IsColimit (Cocone.mk S s)) {j₀ : J}
    {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀} {v₀ : A₀ ⟶ A}
    (hpo : IsPushout (s.app j₀) f₀ g v₀)
    {k : Under j₀} (ĝk : (pushSystem j₀ f₀).obj k) (selk : D.obj k.right)
    (sS : S) (hsel : (coconeι (Cocone.mk S s) k.right).hom selk = sS)
    (gA : A) (hĝ : ((pushCocone hs hpo).ι.app k).hom ĝk = gA)
    (hloc : (letI : Algebra S A := g.hom.toAlgebra
      IsLocalization.Away sS (Localization.Away gA))) :
    ∃ (l : Under j₀) (t : k ⟶ l),
      U1C j₀ f₀ l (((pushSystem j₀ f₀).map t).hom ĝk) ((D.map t.right).hom selk) := by
  letI : Algebra S A := g.hom.toAlgebra
  haveI := hloc
  -- `g sS` is invertible in the localization
  have hsunit : IsUnit (algebraMap A (Localization.Away gA) (g.hom sS)) := by
    have h := IsLocalization.map_units (M := Submonoid.powers sS) (Localization.Away gA)
      ⟨sS, Submonoid.mem_powers sS⟩
    rwa [IsScalarTower.algebraMap_apply S A (Localization.Away gA)] at h
  obtain ⟨z, hz⟩ := hsunit.exists_right_inv
  obtain ⟨yA, dy, hyz⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers gA) z
  obtain ⟨N, hN⟩ := dy.2
  have hN' : gA ^ N = (dy : A) := hN
  have hkey : algebraMap A (Localization.Away gA) (g.hom sS * yA) =
      algebraMap A (Localization.Away gA) (gA ^ N) := by
    have h1 : z * algebraMap A (Localization.Away gA) (gA ^ N) =
        algebraMap A (Localization.Away gA) yA := by
      calc z * algebraMap A (Localization.Away gA) (gA ^ N)
          = IsLocalization.mk' (Localization.Away gA) yA dy *
              algebraMap A (Localization.Away gA) (dy : A) := by rw [hyz, hN']
        _ = algebraMap A (Localization.Away gA) yA := IsLocalization.mk'_spec _ yA dy
    calc algebraMap A (Localization.Away gA) (g.hom sS * yA)
        = algebraMap A (Localization.Away gA) (g.hom sS) *
            algebraMap A (Localization.Away gA) yA := map_mul _ _ _
      _ = algebraMap A (Localization.Away gA) (g.hom sS) *
            (z * algebraMap A (Localization.Away gA) (gA ^ N)) := by rw [h1]
      _ = (algebraMap A (Localization.Away gA) (g.hom sS) * z) *
            algebraMap A (Localization.Away gA) (gA ^ N) := by ring
      _ = algebraMap A (Localization.Away gA) (gA ^ N) := by rw [hz, one_mul]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers gA)
    (Localization.Away gA)).mp hkey
  obtain ⟨M, hM⟩ := c.2
  have hM' : gA ^ M = (c : A) := hM
  rw [← hM'] at hc
  -- find a stage representative for `yA`
  obtain ⟨ky, ŷ₀, hŷ₀⟩ := Concrete.isColimit_exists_rep _ (isColimitPushCocone hs hpo) yA
  -- merge stages
  set l₁ : Under j₀ := IsFiltered.max k ky with hl₁
  set t₁ : k ⟶ l₁ := IsFiltered.leftToMax k ky with ht₁
  set u₁ : ky ⟶ l₁ := IsFiltered.rightToMax k ky with hu₁
  set ĝ₁ := ((pushSystem j₀ f₀).map t₁).hom ĝk with hĝ₁
  set sel₁ := (D.map t₁.right).hom selk with hsel₁
  set ŷ₁ := ((pushSystem j₀ f₀).map u₁).hom ŷ₀ with hŷ₁
  have hŷ₁A : ((pushCocone hs hpo).ι.app l₁).hom ŷ₁ = yA :=
    (pushCocone_w_apply hs hpo u₁ ŷ₀).trans hŷ₀
  have hsel₁S : (coconeι (Cocone.mk S s) l₁.right).hom sel₁ = sS :=
    (coconeι_w_apply (Cocone.mk S s) t₁.right selk).trans hsel
  have hĝ₁A : ((pushCocone hs hpo).ι.app l₁).hom ĝ₁ = gA :=
    (pushCocone_w_apply hs hpo t₁ ĝk).trans hĝ
  set lhs : (pushSystem j₀ f₀).obj l₁ :=
    ĝ₁ ^ M * ((pushInl j₀ f₀ l₁).hom sel₁ * ŷ₁) with hlhs
  set rhs : (pushSystem j₀ f₀).obj l₁ := ĝ₁ ^ (M + N) with hrhs
  have heq : ((pushCocone hs hpo).ι.app l₁).hom lhs =
      ((pushCocone hs hpo).ι.app l₁).hom rhs := by
    rw [hlhs, hrhs, map_mul, map_mul, map_pow, map_pow, hĝ₁A, pushInl_cocone_apply,
      hsel₁S, hŷ₁A, pow_add]
    calc gA ^ M * (g.hom sS * yA) = gA ^ M * gA ^ N := hc
      _ = gA ^ M * gA ^ N := rfl
  obtain ⟨l₂, t₂, ht₂eq⟩ := (IsColimit.eq_iff' (isColimitPushCocone hs hpo) _ _).mp heq
  refine ⟨l₂, t₁ ≫ t₂, ?_⟩
  refine ⟨((pushSystem j₀ f₀).map t₂).hom ŷ₁, N, M, ?_⟩
  have h1 := ht₂eq
  rw [hlhs, hrhs, map_mul, map_mul, map_pow, map_pow, pushInl_map_apply] at h1
  have hcompg : ((pushSystem j₀ f₀).map (t₁ ≫ t₂)).hom ĝk =
      ((pushSystem j₀ f₀).map t₂).hom ĝ₁ := by
    rw [Functor.map_comp]
    rfl
  have hcomps : (D.map (t₁ ≫ t₂).right).hom selk = (D.map t₂.right).hom sel₁ := by
    have h : (t₁ ≫ t₂).right = t₁.right ≫ t₂.right := rfl
    rw [h, D.map_comp]
    rfl
  rw [hcompg, hcomps]
  exact h1

/-- Descend the witness for the inverse of `ĝ`. -/
private lemma exists_e3c (hs : IsColimit (Cocone.mk S s)) {j₀ : J}
    {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀} {v₀ : A₀ ⟶ A}
    (hpo : IsPushout (s.app j₀) f₀ g v₀)
    {k : Under j₀} (ĝk : (pushSystem j₀ f₀).obj k) (selk : D.obj k.right)
    (sS : S) (hsel : (coconeι (Cocone.mk S s) k.right).hom selk = sS)
    (gA : A) (hĝ : ((pushCocone hs hpo).ι.app k).hom ĝk = gA)
    (hloc : (letI : Algebra S A := g.hom.toAlgebra
      IsLocalization.Away sS (Localization.Away gA))) :
    ∃ (l : Under j₀) (t : k ⟶ l),
      E3C j₀ f₀ l (((pushSystem j₀ f₀).map t).hom ĝk) ((D.map t.right).hom selk) := by
  letI : Algebra S A := g.hom.toAlgebra
  haveI := hloc
  -- the inverse of `gA` is a fraction over `S`
  obtain ⟨⟨dS, dsel⟩, hsurj⟩ := IsLocalization.surj (M := Submonoid.powers sS)
    (S := Localization.Away gA)
    (IsLocalization.mk' (Localization.Away gA) (1 : A) ⟨gA, Submonoid.mem_powers gA⟩)
  obtain ⟨n, hn⟩ := dsel.2
  have hn' : sS ^ n = (dsel : S) := hn
  have hA : algebraMap A (Localization.Away gA) (g.hom (sS ^ n)) =
      algebraMap A (Localization.Away gA) (g.hom dS * gA) := by
    have hms : IsLocalization.mk' (Localization.Away gA) (1 : A)
        (⟨gA, Submonoid.mem_powers gA⟩ : Submonoid.powers gA) *
        algebraMap A (Localization.Away gA) gA = 1 := by
      have := IsLocalization.mk'_spec (Localization.Away gA) (1 : A)
        (⟨gA, Submonoid.mem_powers gA⟩ : Submonoid.powers gA)
      simp
    have h1 : algebraMap S (Localization.Away gA) ((dsel : S)) =
        algebraMap A (Localization.Away gA) (g.hom (sS ^ n)) := by
      rw [IsScalarTower.algebraMap_apply S A (Localization.Away gA), hn']
      rfl
    have h2 : algebraMap S (Localization.Away gA) dS =
        algebraMap A (Localization.Away gA) (g.hom dS) := by
      rw [IsScalarTower.algebraMap_apply S A (Localization.Away gA)]
      rfl
    calc algebraMap A (Localization.Away gA) (g.hom (sS ^ n))
        = 1 * algebraMap A (Localization.Away gA) (g.hom (sS ^ n)) := by rw [one_mul]
      _ = (IsLocalization.mk' (Localization.Away gA) (1 : A)
            (⟨gA, Submonoid.mem_powers gA⟩ : Submonoid.powers gA) *
            algebraMap A (Localization.Away gA) gA) *
            algebraMap A (Localization.Away gA) (g.hom (sS ^ n)) := by rw [hms]
      _ = (IsLocalization.mk' (Localization.Away gA) (1 : A)
            (⟨gA, Submonoid.mem_powers gA⟩ : Submonoid.powers gA) *
            algebraMap S (Localization.Away gA) ((dsel : S))) *
            algebraMap A (Localization.Away gA) gA := by rw [h1]; ring
      _ = algebraMap S (Localization.Away gA) dS *
            algebraMap A (Localization.Away gA) gA := by rw [hsurj]
      _ = algebraMap A (Localization.Away gA) (g.hom dS * gA) := by rw [h2, map_mul]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers gA)
    (Localization.Away gA)).mp hA
  obtain ⟨M, hM⟩ := c.2
  have hM' : gA ^ M = (c : A) := hM
  rw [← hM'] at hc
  -- find a stage representative for `dS`
  obtain ⟨j₁, d₁, hd₁⟩ := coconeι_exists_rep (Cocone.mk S s) hs dS
  set l₁ : Under j₀ := Under.mk (k.hom ≫ IsFiltered.leftToMax k.right j₁) with hl₁
  set t₁ : k ⟶ l₁ := Under.homMk (IsFiltered.leftToMax k.right j₁) rfl with ht₁
  set d₂ : D.obj l₁.right := (D.map (IsFiltered.rightToMax k.right j₁)).hom d₁ with hd₂
  have hd₂S : (coconeι (Cocone.mk S s) l₁.right).hom d₂ = dS :=
    (coconeι_w_apply (Cocone.mk S s) (IsFiltered.rightToMax k.right j₁) d₁).trans hd₁
  set ĝ₁ := ((pushSystem j₀ f₀).map t₁).hom ĝk with hĝ₁
  set sel₁ := (D.map t₁.right).hom selk with hsel₁
  have hsel₁S : (coconeι (Cocone.mk S s) l₁.right).hom sel₁ = sS :=
    (coconeι_w_apply (Cocone.mk S s) t₁.right selk).trans hsel
  have hĝ₁A : ((pushCocone hs hpo).ι.app l₁).hom ĝ₁ = gA :=
    (pushCocone_w_apply hs hpo t₁ ĝk).trans hĝ
  set lhs : (pushSystem j₀ f₀).obj l₁ :=
    ĝ₁ ^ M * (pushInl j₀ f₀ l₁).hom (sel₁ ^ n) with hlhs
  set rhs : (pushSystem j₀ f₀).obj l₁ :=
    ĝ₁ ^ M * ((pushInl j₀ f₀ l₁).hom d₂ * ĝ₁) with hrhs
  have heq : ((pushCocone hs hpo).ι.app l₁).hom lhs =
      ((pushCocone hs hpo).ι.app l₁).hom rhs := by
    rw [hlhs, hrhs, map_mul, map_mul, map_mul, map_pow, hĝ₁A, pushInl_cocone_apply,
      pushInl_cocone_apply, hd₂S, map_pow, hsel₁S]
    exact hc
  obtain ⟨l₂, t₂, ht₂eq⟩ := (IsColimit.eq_iff' (isColimitPushCocone hs hpo) _ _).mp heq
  refine ⟨l₂, t₁ ≫ t₂, ?_⟩
  refine ⟨(D.map t₂.right).hom d₂, n, M, ?_⟩
  have h1 := ht₂eq
  rw [hlhs, hrhs, map_mul, map_mul, map_mul, map_pow, pushInl_map_apply, pushInl_map_apply,
    map_pow] at h1
  have hcompg : ((pushSystem j₀ f₀).map (t₁ ≫ t₂)).hom ĝk =
      ((pushSystem j₀ f₀).map t₂).hom ĝ₁ := by
    rw [Functor.map_comp]
    rfl
  have hcomps : (D.map (t₁ ≫ t₂).right).hom selk = (D.map t₂.right).hom sel₁ := by
    have h : (t₁ ≫ t₂).right = t₁.right ≫ t₂.right := rfl
    rw [h, D.map_comp]
    rfl
  rw [hcompg, hcomps]
  exact h1

/-- Descend the surjectivity witnesses for a finite set of elements of `A₀`. -/
private lemma exists_e2c_batch (hs : IsColimit (Cocone.mk S s)) {j₀ : J}
    {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀} {v₀ : A₀ ⟶ A}
    (hpo : IsPushout (s.app j₀) f₀ g v₀) (G : Finset A₀)
    {k : Under j₀} (ĝk : (pushSystem j₀ f₀).obj k) (selk : D.obj k.right)
    (sS : S) (hsel : (coconeι (Cocone.mk S s) k.right).hom selk = sS)
    (gA : A) (hĝ : ((pushCocone hs hpo).ι.app k).hom ĝk = gA)
    (hloc : (letI : Algebra S A := g.hom.toAlgebra
      IsLocalization.Away sS (Localization.Away gA))) :
    ∃ (l : Under j₀) (t : k ⟶ l), ∀ a ∈ G,
      E2C j₀ f₀ l (((pushSystem j₀ f₀).map t).hom ĝk) ((D.map t.right).hom selk) a := by
  classical
  induction G using Finset.induction_on with
  | empty => exact ⟨k, 𝟙 k, fun a ha ↦ absurd ha (Finset.notMem_empty a)⟩
  | insert a G' ha ih =>
      obtain ⟨l₁, t₁, h₁⟩ := ih
      have hsel₁ : (coconeι (Cocone.mk S s) l₁.right).hom ((D.map t₁.right).hom selk) = sS :=
        (coconeι_w_apply (Cocone.mk S s) t₁.right selk).trans hsel
      have hĝ₁ : ((pushCocone hs hpo).ι.app l₁).hom
          (((pushSystem j₀ f₀).map t₁).hom ĝk) = gA :=
        (pushCocone_w_apply hs hpo t₁ ĝk).trans hĝ
      obtain ⟨l₂, t₂, h₂⟩ := exists_e2c hs hpo (((pushSystem j₀ f₀).map t₁).hom ĝk)
        ((D.map t₁.right).hom selk) a sS hsel₁ gA hĝ₁ hloc
      refine ⟨l₂, t₁ ≫ t₂, ?_⟩
      have hcompg : ((pushSystem j₀ f₀).map (t₁ ≫ t₂)).hom ĝk =
          ((pushSystem j₀ f₀).map t₂).hom (((pushSystem j₀ f₀).map t₁).hom ĝk) := by
        rw [Functor.map_comp]
        rfl
      have hcomps : (D.map (t₁ ≫ t₂).right).hom selk =
          (D.map t₂.right).hom ((D.map t₁.right).hom selk) := by
        have h : (t₁ ≫ t₂).right = t₁.right ≫ t₂.right := rfl
        rw [h, D.map_comp]
        rfl
      rw [hcompg, hcomps]
      intro x hx
      rcases Finset.mem_insert.mp hx with hxa | hxG
      · subst hxa
        exact h₂
      · exact (h₁ x hxG).push t₂

omit [IsFiltered J] in
private lemma awaySystemCocone_w_apply (c : Cocone D) (j' : J) (r : D.obj j')
    {m m' : Under j'} (u : m ⟶ m') (x : Localization.Away (rAt j' r m)) :
    ((awaySystemCocone c j' r).ι.app m').hom (((awaySystem (D := D) j' r).map u).hom x) =
      ((awaySystemCocone c j' r).ι.app m).hom x := by
  calc ((awaySystemCocone c j' r).ι.app m').hom (((awaySystem (D := D) j' r).map u).hom x)
      = ((awaySystem (D := D) j' r).map u ≫ (awaySystemCocone c j' r).ι.app m').hom x := rfl
    _ = ((awaySystemCocone c j' r).ι.app m).hom x :=
        congrArg (fun q ↦ q.hom x) ((awaySystemCocone c j' r).w u)

omit [IsFiltered J] in
/-- Generalized form of `pieceChi_push` with an arbitrary target element. -/
private lemma pieceChi_push' {j₀ : J} {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀}
    {k : Under j₀} (selt : D.obj k.right) (q : A₀ ⟶ CommRingCat.of (Localization.Away selt))
    (hq : f₀ ≫ q =
      D.map k.hom ≫ CommRingCat.ofHom (algebraMap (D.obj k.right) (Localization.Away selt)))
    {l : Under j₀} (t : k ⟶ l) (selt' : D.obj l.right) (h : (D.map t.right).hom selt = selt')
    (hq' : f₀ ≫ q ≫ awayLift (D.map t.right) selt selt' h =
      D.map l.hom ≫ CommRingCat.ofHom (algebraMap (D.obj l.right) (Localization.Away selt'))) :
    (pushSystem j₀ f₀).map t ≫ pieceChi f₀ l selt'
        (q ≫ awayLift (D.map t.right) selt selt' h) hq' =
      pieceChi f₀ k selt q hq ≫ awayLift (D.map t.right) selt selt' h := by
  apply (pushSquare j₀ f₀ k).hom_ext
  · refine CommRingCat.hom_ext (RingHom.ext fun b ↦ ?_)
    change (pieceChi f₀ l selt' _ hq').hom
        (((pushSystem j₀ f₀).map t).hom ((pushInl j₀ f₀ k).hom b)) =
      (awayLift (D.map t.right) selt selt' h).hom
        ((pieceChi f₀ k selt q hq).hom ((pushInl j₀ f₀ k).hom b))
    rw [pushInl_map_apply, pieceChi_inl, pieceChi_inl, awayLift_algebraMap]
  · refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
    change (pieceChi f₀ l selt' _ hq').hom
        (((pushSystem j₀ f₀).map t).hom ((pushInr j₀ f₀ k).hom a)) =
      (awayLift (D.map t.right) selt selt' h).hom
        ((pieceChi f₀ k selt q hq).hom ((pushInr j₀ f₀ k).hom a))
    rw [pushInr_map_apply, pieceChi_inr, pieceChi_inr]
    rfl

set_option maxHeartbeats 1600000 in
-- The proof descends many pieces of data stage by stage through a long chain of filtered
-- colimit arguments, which exceeds the default heartbeat limit.
/-- Descend all the piece data to a single stage. -/
private lemma exists_pieceAt (hs : IsColimit (Cocone.mk S s)) {j₀ : J}
    {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀} {v₀ : A₀ ⟶ A}
    (hpo : IsPushout (s.app j₀) f₀ g v₀)
    (hfp : MorphismProperty.isFinitelyPresentable.{u} CommRingCat.{u} f₀)
    (gens : Finset A₀)
    {k₀ : Under j₀} (ĝ₀ : (pushSystem j₀ f₀).obj k₀)
    (gA : A) (hgA0 : ((pushCocone hs hpo).ι.app k₀).hom ĝ₀ = gA)
    (hstd : (letI : Algebra S A := g.hom.toAlgebra
      Algebra.IsStandardOpenImmersion S (Localization.Away gA))) :
    ∃ (k : Under j₀) (t : k₀ ⟶ k),
      Nonempty (PieceAt j₀ f₀ gens k (((pushSystem j₀ f₀).map t).hom ĝ₀)) := by
  classical
  letI : Algebra S A := g.hom.toAlgebra
  obtain ⟨sS₀, hloc₀⟩ := hstd.exists_away
  -- stage representative for `sS₀`
  obtain ⟨j₁, ŝ₀, hŝ₀⟩ := coconeι_exists_rep (Cocone.mk S s) hs sS₀
  let k₁ : Under j₀ := ⟨⟨⟨⟩⟩, IsFiltered.max k₀.right j₁, k₀.hom ≫ IsFiltered.leftToMax k₀.right j₁⟩
  let t₁ : k₀ ⟶ k₁ := Under.homMk (IsFiltered.leftToMax k₀.right j₁) rfl
  let ŝ : D.obj k₁.right := (D.map (IsFiltered.rightToMax k₀.right j₁)).hom ŝ₀
  have hŝS : (coconeι (Cocone.mk S s) k₁.right).hom ŝ = sS₀ :=
    (coconeι_w_apply (Cocone.mk S s) (IsFiltered.rightToMax k₀.right j₁) ŝ₀).trans hŝ₀
  subst hŝS
  -- `gA` is given as a hypothesis
  haveI hloc : IsLocalization.Away ((coconeι (Cocone.mk S s) k₁.right).hom ŝ)
      (Localization.Away gA) := hloc₀
  -- the canonical equivalence between the two localization models
  let e : Localization.Away ((coconeι (Cocone.mk S s) k₁.right).hom ŝ) ≃ₐ[S]
      Localization.Away gA :=
    IsLocalization.algEquiv
      (Submonoid.powers ((coconeι (Cocone.mk S s) k₁.right).hom ŝ)) _ _
  let f'' : A₀ ⟶ CommRingCat.of
      (Localization.Away ((coconeι (Cocone.mk S s) k₁.right).hom ŝ)) :=
    CommRingCat.ofHom (e.symm.toAlgHom.toRingHom.comp
      ((algebraMap A (Localization.Away gA)).comp v₀.hom))
  -- descend the inverse morphism on `A₀`
  let s'' : (Functor.const (Under k₁.right)).obj (D.obj j₀) ⟶ awaySystem (D := D) k₁.right ŝ :=
    { app := fun m ↦ D.map (k₁.hom ≫ m.hom) ≫
        CommRingCat.ofHom (algebraMap (D.obj m.right) (Localization.Away (rAt k₁.right ŝ m)))
      naturality := fun m m' w ↦ by
        refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
        change algebraMap (D.obj m'.right) (Localization.Away (rAt k₁.right ŝ m'))
            ((D.map (k₁.hom ≫ m'.hom)).hom r) =
          (awayLift (D.map w.right) _ _ (rAt_map k₁.right ŝ w)).hom
            (algebraMap (D.obj m.right) (Localization.Away (rAt k₁.right ŝ m))
              ((D.map (k₁.hom ≫ m.hom)).hom r))
        rw [awayLift_algebraMap]
        congr 1
        have harr : k₁.hom ≫ m'.hom = (k₁.hom ≫ m.hom) ≫ Under.Hom.right w :=
          ((Category.assoc _ _ _).trans (whisker_eq k₁.hom (Under.w w))).symm
        calc (D.map (k₁.hom ≫ m'.hom)).hom r
            = (D.map ((k₁.hom ≫ m.hom) ≫ Under.Hom.right w)).hom r := by rw [harr]
          _ = (D.map w.right).hom ((D.map (k₁.hom ≫ m.hom)).hom r) := by
              rw [D.map_comp]
              rfl }
  have h'' : ∀ m : Under k₁.right,
      s''.app m ≫ (awaySystemCocone (Cocone.mk S s) k₁.right ŝ).ι.app m = f₀ ≫ f'' := by
    intro m
    refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
    change (awayLift (coconeι (Cocone.mk S s) m.right) _ _ (rAt_cocone k₁.right ŝ m)).hom
        (algebraMap (D.obj m.right) (Localization.Away (rAt k₁.right ŝ m))
          ((D.map (k₁.hom ≫ m.hom)).hom r)) =
      e.symm (algebraMap A (Localization.Away gA) (v₀.hom (f₀.hom r)))
    rw [awayLift_algebraMap]
    have h1 : (coconeι (Cocone.mk S s) m.right).hom ((D.map (k₁.hom ≫ m.hom)).hom r) =
        (coconeι (Cocone.mk S s) j₀).hom r :=
      coconeι_w_apply (Cocone.mk S s) (k₁.hom ≫ m.hom) r
    have h2 : v₀.hom (f₀.hom r) = g.hom ((coconeι (Cocone.mk S s) j₀).hom r) := by
      calc v₀.hom (f₀.hom r) = (f₀ ≫ v₀).hom r := rfl
        _ = (s.app j₀ ≫ g).hom r := congrArg (fun q ↦ q.hom r) hpo.w.symm
        _ = g.hom ((coconeι (Cocone.mk S s) j₀).hom r) := rfl
    rw [h1, h2]
    have h3 : algebraMap A (Localization.Away gA)
        (g.hom ((coconeι (Cocone.mk S s) j₀).hom r)) =
        algebraMap S (Localization.Away gA) ((coconeι (Cocone.mk S s) j₀).hom r) := by
      rw [IsScalarTower.algebraMap_apply S A (Localization.Away gA)]
      rfl
    rw [h3]
    exact (e.symm.commutes ((coconeι (Cocone.mk S s) j₀).hom r)).symm
  obtain ⟨mq, q', hq'1, hq'2⟩ := MorphismProperty.exists_hom_of_isFinitelyPresentable
    (isColimitAwaySystemCocone hs k₁.right ŝ) hfp s'' f'' h''
  -- merge into a stage over `j₀`
  let k₂ : Under j₀ := ⟨⟨⟨⟩⟩, mq.right, k₁.hom ≫ mq.hom⟩
  let t₂ : k₁ ⟶ k₂ := Under.homMk mq.hom rfl
  have hq₂ : f₀ ≫ q' = D.map k₂.hom ≫ CommRingCat.ofHom
      (algebraMap (D.obj k₂.right) (Localization.Away (rAt k₁.right ŝ mq))) := hq'1
  -- the χ-map at this stage and its colimit value
  have hĝ₂A : ((pushCocone hs hpo).ι.app k₂).hom
      (((pushSystem j₀ f₀).map (t₁ ≫ t₂)).hom ĝ₀) = gA :=
    (pushCocone_w_apply hs hpo (t₁ ≫ t₂) ĝ₀).trans hgA0
  have hχc : pieceChi f₀ k₂ (rAt k₁.right ŝ mq) q' hq₂ ≫
      (awaySystemCocone (Cocone.mk S s) k₁.right ŝ).ι.app mq =
      (pushCocone hs hpo).ι.app k₂ ≫ CommRingCat.ofHom
        (e.symm.toAlgHom.toRingHom.comp (algebraMap A (Localization.Away gA))) := by
    apply (pushSquare j₀ f₀ k₂).hom_ext
    · refine CommRingCat.hom_ext (RingHom.ext fun b ↦ ?_)
      change (awayLift (coconeι (Cocone.mk S s) mq.right) _ _ (rAt_cocone k₁.right ŝ mq)).hom
          ((pieceChi f₀ k₂ (rAt k₁.right ŝ mq) q' hq₂).hom ((pushInl j₀ f₀ k₂).hom b)) =
        e.symm (algebraMap A (Localization.Away gA)
          (((pushCocone hs hpo).ι.app k₂).hom ((pushInl j₀ f₀ k₂).hom b)))
      rw [pieceChi_inl, awayLift_algebraMap, pushInl_cocone_apply]
      have h3 : algebraMap A (Localization.Away gA)
          (g.hom ((coconeι (Cocone.mk S s) k₂.right).hom b)) =
          algebraMap S (Localization.Away gA) ((coconeι (Cocone.mk S s) k₂.right).hom b) := by
        rw [IsScalarTower.algebraMap_apply S A (Localization.Away gA)]
        rfl
      rw [h3]
      exact (e.symm.commutes ((coconeι (Cocone.mk S s) k₂.right).hom b)).symm
    · refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
      change (awayLift (coconeι (Cocone.mk S s) mq.right) _ _ (rAt_cocone k₁.right ŝ mq)).hom
          ((pieceChi f₀ k₂ (rAt k₁.right ŝ mq) q' hq₂).hom ((pushInr j₀ f₀ k₂).hom a)) =
        e.symm (algebraMap A (Localization.Away gA)
          (((pushCocone hs hpo).ι.app k₂).hom ((pushInr j₀ f₀ k₂).hom a)))
      rw [pieceChi_inr, pushInr_cocone_apply]
      exact congrArg (fun m ↦ m.hom a) hq'2
  -- invertibility of the χ-image of `ĝ` at the colimit level
  have hgu : IsUnit (e.symm (algebraMap A (Localization.Away gA) gA)) :=
    (IsLocalization.Away.algebraMap_isUnit gA).map e.symm
  obtain ⟨zInf, hzInf⟩ := hgu.exists_right_inv
  obtain ⟨mz, zhat, hzhat⟩ := awaySystem_exists_rep hs k₁.right ŝ zInf
  -- merge the two stages over `k₁.right`
  let m₃ : Under k₁.right := IsFiltered.max mq mz
  let uq : mq ⟶ m₃ := IsFiltered.leftToMax mq mz
  let uz : mz ⟶ m₃ := IsFiltered.rightToMax mq mz
  set xq := ((awaySystem (D := D) k₁.right ŝ).map uq).hom
    ((pieceChi f₀ k₂ (rAt k₁.right ŝ mq) q' hq₂).hom
      (((pushSystem j₀ f₀).map (t₁ ≫ t₂)).hom ĝ₀)) with hxq
  set xz := ((awaySystem (D := D) k₁.right ŝ).map uz).hom zhat with hxz
  have heqU2 : ((awaySystemCocone (Cocone.mk S s) k₁.right ŝ).ι.app m₃).hom (xq * xz) =
      ((awaySystemCocone (Cocone.mk S s) k₁.right ŝ).ι.app m₃).hom 1 := by
    rw [map_mul, map_one, hxq, hxz, awaySystemCocone_w_apply, awaySystemCocone_w_apply, hzhat]
    have h1 : ((awaySystemCocone (Cocone.mk S s) k₁.right ŝ).ι.app mq).hom
        ((pieceChi f₀ k₂ (rAt k₁.right ŝ mq) q' hq₂).hom
          (((pushSystem j₀ f₀).map (t₁ ≫ t₂)).hom ĝ₀)) =
        e.symm (algebraMap A (Localization.Away gA) gA) := by
      have h2 := congrArg (fun m ↦ m.hom (((pushSystem j₀ f₀).map (t₁ ≫ t₂)).hom ĝ₀)) hχc
      refine Eq.trans (Eq.trans rfl h2) ?_
      change e.symm (algebraMap A (Localization.Away gA)
        (((pushCocone hs hpo).ι.app k₂).hom (((pushSystem j₀ f₀).map (t₁ ≫ t₂)).hom ĝ₀))) = _
      rw [hĝ₂A]
    rw [h1]
    exact hzInf
  obtain ⟨m₄, v, hv⟩ := awaySystem_exists_map_eq hs k₁.right ŝ m₃ _ _ heqU2
  -- the final stage
  let k₃ : Under j₀ := ⟨⟨⟨⟩⟩, m₄.right, k₁.hom ≫ m₄.hom⟩
  have htri : mq.hom ≫ (uq ≫ v).right = m₄.hom := Under.w (uq ≫ v)
  let t₃ : k₂ ⟶ k₃ := Under.homMk (uq ≫ v).right
    (by change (k₁.hom ≫ mq.hom) ≫ (uq ≫ v).right = k₁.hom ≫ m₄.hom
        rw [Category.assoc, htri])
  have hsel₃ : (D.map t₃.right).hom (rAt k₁.right ŝ mq) = rAt k₁.right ŝ m₄ :=
    rAt_map k₁.right ŝ (uq ≫ v)
  let q₃ : A₀ ⟶ CommRingCat.of (Localization.Away (rAt k₁.right ŝ m₄)) :=
    q' ≫ awayLift (D.map (uq ≫ v).right) (rAt k₁.right ŝ mq) (rAt k₁.right ŝ m₄) hsel₃
  have hq₃ : f₀ ≫ q₃ = D.map k₃.hom ≫ CommRingCat.ofHom
      (algebraMap (D.obj k₃.right) (Localization.Away (rAt k₁.right ŝ m₄))) := by
    refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
    change (awayLift (D.map (uq ≫ v).right) _ _ hsel₃).hom (q'.hom (f₀.hom r)) =
      algebraMap (D.obj k₃.right) (Localization.Away (rAt k₁.right ŝ m₄))
        ((D.map k₃.hom).hom r)
    have h1 : q'.hom (f₀.hom r) = algebraMap (D.obj k₂.right)
        (Localization.Away (rAt k₁.right ŝ mq)) ((D.map k₂.hom).hom r) :=
      congrArg (fun m ↦ m.hom r) hq₂
    rw [h1, awayLift_algebraMap]
    congr 1
    calc (D.map (uq ≫ v).right).hom ((D.map k₂.hom).hom r)
        = (D.map k₂.hom ≫ D.map (uq ≫ v).right).hom r := rfl
      _ = (D.map k₃.hom).hom r := by
          rw [← D.map_comp]
          change (D.map ((k₁.hom ≫ mq.hom) ≫ (uq ≫ v).right)).hom r = _
          rw [Category.assoc, htri]
  -- now descend the remaining witnesses, starting from `k₃`
  set ĝ₃ := ((pushSystem j₀ f₀).map (t₁ ≫ t₂ ≫ t₃)).hom ĝ₀ with hĝ₃
  have hĝ₃' : ĝ₃ = ((pushSystem j₀ f₀).map t₃).hom
      (((pushSystem j₀ f₀).map (t₁ ≫ t₂)).hom ĝ₀) := by
    rw [hĝ₃]
    have h : t₁ ≫ t₂ ≫ t₃ = (t₁ ≫ t₂) ≫ t₃ := by rw [Category.assoc]
    rw [h, Functor.map_comp]
    rfl
  have hĝ₃A : ((pushCocone hs hpo).ι.app k₃).hom ĝ₃ = gA := by
    rw [hĝ₃']
    exact (pushCocone_w_apply hs hpo t₃ _).trans hĝ₂A
  have hsel₃S : (coconeι (Cocone.mk S s) k₃.right).hom (rAt k₁.right ŝ m₄) =
      (coconeι (Cocone.mk S s) k₁.right).hom ŝ :=
    rAt_cocone k₁.right ŝ m₄
  -- the `U2` witness at `k₃`
  let u2z₃ : Localization.Away (rAt k₁.right ŝ m₄) :=
    ((awaySystem (D := D) k₁.right ŝ).map (uz ≫ v)).hom zhat
  have hu2₃ : (pieceChi f₀ k₃ (rAt k₁.right ŝ m₄) q₃ hq₃).hom ĝ₃ * u2z₃ = 1 := by
    have hχmor : (pushSystem j₀ f₀).map t₃ ≫ pieceChi f₀ k₃ (rAt k₁.right ŝ m₄) q₃ hq₃ =
        pieceChi f₀ k₂ (rAt k₁.right ŝ mq) q' hq₂ ≫
          awayLift (D.map (uq ≫ v).right) (rAt k₁.right ŝ mq) (rAt k₁.right ŝ m₄) hsel₃ := by
      apply (pushSquare j₀ f₀ k₂).hom_ext
      · refine CommRingCat.hom_ext (RingHom.ext fun b ↦ ?_)
        change (pieceChi f₀ k₃ (rAt k₁.right ŝ m₄) q₃ hq₃).hom
            (((pushSystem j₀ f₀).map t₃).hom ((pushInl j₀ f₀ k₂).hom b)) =
          (awayLift (D.map (uq ≫ v).right) _ _ hsel₃).hom
            ((pieceChi f₀ k₂ (rAt k₁.right ŝ mq) q' hq₂).hom ((pushInl j₀ f₀ k₂).hom b))
        rw [pushInl_map_apply, pieceChi_inl, pieceChi_inl, awayLift_algebraMap]
        rfl
      · refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
        change (pieceChi f₀ k₃ (rAt k₁.right ŝ m₄) q₃ hq₃).hom
            (((pushSystem j₀ f₀).map t₃).hom ((pushInr j₀ f₀ k₂).hom a)) =
          (awayLift (D.map (uq ≫ v).right) _ _ hsel₃).hom
            ((pieceChi f₀ k₂ (rAt k₁.right ŝ mq) q' hq₂).hom ((pushInr j₀ f₀ k₂).hom a))
        rw [pushInr_map_apply, pieceChi_inr, pieceChi_inr]
        rfl
    have hχval : (pieceChi f₀ k₃ (rAt k₁.right ŝ m₄) q₃ hq₃).hom ĝ₃ =
        ((awaySystem (D := D) k₁.right ŝ).map (uq ≫ v)).hom
          ((pieceChi f₀ k₂ (rAt k₁.right ŝ mq) q' hq₂).hom
            (((pushSystem j₀ f₀).map (t₁ ≫ t₂)).hom ĝ₀)) := by
      rw [hĝ₃']
      exact congrArg (fun m ↦ m.hom (((pushSystem j₀ f₀).map (t₁ ≫ t₂)).hom ĝ₀)) hχmor
    rw [hχval]
    have hv' : ((awaySystem (D := D) k₁.right ŝ).map v).hom (xq * xz) =
        ((awaySystem (D := D) k₁.right ŝ).map v).hom 1 := hv
    rw [map_mul, map_one, hxq, hxz] at hv'
    have hcompq : ((awaySystem (D := D) k₁.right ŝ).map (uq ≫ v)).hom
        ((pieceChi f₀ k₂ (rAt k₁.right ŝ mq) q' hq₂).hom
          (((pushSystem j₀ f₀).map (t₁ ≫ t₂)).hom ĝ₀)) =
        ((awaySystem (D := D) k₁.right ŝ).map v).hom
          (((awaySystem (D := D) k₁.right ŝ).map uq).hom
            ((pieceChi f₀ k₂ (rAt k₁.right ŝ mq) q' hq₂).hom
              (((pushSystem j₀ f₀).map (t₁ ≫ t₂)).hom ĝ₀))) := by
      rw [Functor.map_comp]
      rfl
    have hcompz : ((awaySystem (D := D) k₁.right ŝ).map (uz ≫ v)).hom zhat =
        ((awaySystem (D := D) k₁.right ŝ).map v).hom
          (((awaySystem (D := D) k₁.right ŝ).map uz).hom zhat) := by
      rw [Functor.map_comp]
      rfl
    change ((awaySystem (D := D) k₁.right ŝ).map (uq ≫ v)).hom
        ((pieceChi f₀ k₂ (rAt k₁.right ŝ mq) q' hq₂).hom
          (((pushSystem j₀ f₀).map (t₁ ≫ t₂)).hom ĝ₀)) *
      ((awaySystem (D := D) k₁.right ŝ).map (uz ≫ v)).hom zhat = 1
    rw [hcompq, hcompz]
    exact hv'
  -- descend `U1`
  obtain ⟨k₄, t₄, hu1₄⟩ := exists_u1c hs hpo ĝ₃ (rAt k₁.right ŝ m₄)
    ((coconeι (Cocone.mk S s) k₁.right).hom ŝ) hsel₃S gA hĝ₃A hloc
  -- descend `E3`
  have hsel₄S : (coconeι (Cocone.mk S s) k₄.right).hom
      ((D.map t₄.right).hom (rAt k₁.right ŝ m₄)) =
      (coconeι (Cocone.mk S s) k₁.right).hom ŝ :=
    (coconeι_w_apply (Cocone.mk S s) t₄.right _).trans hsel₃S
  have hĝ₄A : ((pushCocone hs hpo).ι.app k₄).hom
      (((pushSystem j₀ f₀).map t₄).hom ĝ₃) = gA :=
    (pushCocone_w_apply hs hpo t₄ ĝ₃).trans hĝ₃A
  obtain ⟨k₅, t₅, he3₅⟩ := exists_e3c hs hpo (((pushSystem j₀ f₀).map t₄).hom ĝ₃)
    ((D.map t₄.right).hom (rAt k₁.right ŝ m₄))
    ((coconeι (Cocone.mk S s) k₁.right).hom ŝ) hsel₄S gA hĝ₄A hloc
  -- descend `E2` for all generators
  have hsel₅S : (coconeι (Cocone.mk S s) k₅.right).hom
      ((D.map t₅.right).hom ((D.map t₄.right).hom (rAt k₁.right ŝ m₄))) =
      (coconeι (Cocone.mk S s) k₁.right).hom ŝ :=
    (coconeι_w_apply (Cocone.mk S s) t₅.right _).trans hsel₄S
  have hĝ₅A : ((pushCocone hs hpo).ι.app k₅).hom
      (((pushSystem j₀ f₀).map t₅).hom (((pushSystem j₀ f₀).map t₄).hom ĝ₃)) = gA :=
    (pushCocone_w_apply hs hpo t₅ _).trans hĝ₄A
  obtain ⟨k₆, t₆, he2₆⟩ := exists_e2c_batch hs hpo gens
    (((pushSystem j₀ f₀).map t₅).hom (((pushSystem j₀ f₀).map t₄).hom ĝ₃))
    ((D.map t₅.right).hom ((D.map t₄.right).hom (rAt k₁.right ŝ m₄)))
    ((coconeι (Cocone.mk S s) k₁.right).hom ŝ) hsel₅S gA hĝ₅A hloc
  -- assemble the piece data at `k₆`
  -- push the `q` and `U2` data up to `k₆`
  let q₄ := q₃ ≫ awayLift (D.map t₄.right) (rAt k₁.right ŝ m₄) _ rfl
  have hq₄ := pieceAt_push_hq (k := k₃) (rAt k₁.right ŝ m₄) q₃ hq₃ t₄
  let q₅ := q₄ ≫ awayLift (D.map t₅.right) ((D.map t₄.right).hom (rAt k₁.right ŝ m₄)) _ rfl
  have hq₅ := pieceAt_push_hq (k := k₄) ((D.map t₄.right).hom (rAt k₁.right ŝ m₄)) q₄ hq₄ t₅
  let q₆ := q₅ ≫ awayLift (D.map t₆.right)
    ((D.map t₅.right).hom ((D.map t₄.right).hom (rAt k₁.right ŝ m₄))) _ rfl
  have hq₆ := pieceAt_push_hq (k := k₅)
    ((D.map t₅.right).hom ((D.map t₄.right).hom (rAt k₁.right ŝ m₄))) q₅ hq₅ t₆
  set ĝ₄ := ((pushSystem j₀ f₀).map t₄).hom ĝ₃ with hĝ₄
  set ĝ₅ := ((pushSystem j₀ f₀).map t₅).hom ĝ₄ with hĝ₅
  set ĝ₆ := ((pushSystem j₀ f₀).map t₆).hom ĝ₅ with hĝ₆
  have hu2₄ : (pieceChi f₀ k₄ ((D.map t₄.right).hom (rAt k₁.right ŝ m₄)) q₄ hq₄).hom ĝ₄ *
      (awayLift (D.map t₄.right) (rAt k₁.right ŝ m₄) _ rfl).hom u2z₃ = 1 := by
    rw [hĝ₄, pieceChi_push_apply (k := k₃) (rAt k₁.right ŝ m₄) q₃ hq₃ t₄ ĝ₃, ← map_mul, hu2₃,
      map_one]
  have hu2₅ : (pieceChi f₀ k₅
      ((D.map t₅.right).hom ((D.map t₄.right).hom (rAt k₁.right ŝ m₄))) q₅ hq₅).hom ĝ₅ *
      (awayLift (D.map t₅.right) ((D.map t₄.right).hom (rAt k₁.right ŝ m₄)) _ rfl).hom
        ((awayLift (D.map t₄.right) (rAt k₁.right ŝ m₄) _ rfl).hom u2z₃) = 1 := by
    rw [hĝ₅, pieceChi_push_apply (k := k₄) ((D.map t₄.right).hom (rAt k₁.right ŝ m₄)) q₄ hq₄ t₅ ĝ₄,
      ← map_mul, hu2₄, map_one]
  have hu2₆ : (pieceChi f₀ k₆
      ((D.map t₆.right).hom ((D.map t₅.right).hom
        ((D.map t₄.right).hom (rAt k₁.right ŝ m₄)))) q₆ hq₆).hom ĝ₆ *
      (awayLift (D.map t₆.right)
        ((D.map t₅.right).hom ((D.map t₄.right).hom (rAt k₁.right ŝ m₄))) _ rfl).hom
        ((awayLift (D.map t₅.right) ((D.map t₄.right).hom (rAt k₁.right ŝ m₄)) _ rfl).hom
          ((awayLift (D.map t₄.right) (rAt k₁.right ŝ m₄) _ rfl).hom u2z₃)) = 1 := by
    rw [hĝ₆, pieceChi_push_apply (k := k₅) ((D.map t₅.right).hom ((D.map t₄.right).hom
      (rAt k₁.right ŝ m₄))) q₅ hq₅ t₆ ĝ₅, ← map_mul, hu2₅, map_one]
  -- transport along the composite
  have heq : ((pushSystem j₀ f₀).map (t₁ ≫ t₂ ≫ t₃ ≫ t₄ ≫ t₅ ≫ t₆)).hom ĝ₀ = ĝ₆ := by
    rw [hĝ₆, hĝ₅, hĝ₄, hĝ₃]
    simp only [Functor.map_comp]
    rfl
  obtain ⟨u1y₆, u1N₆, u1M₆, hu1₆⟩ := (hu1₄.push t₅).push t₆
  have he3₆ := he3₅.push t₆
  have P6 : PieceAt j₀ f₀ gens k₆ ĝ₆ :=
    ⟨(D.map t₆.right).hom ((D.map t₅.right).hom ((D.map t₄.right).hom (rAt k₁.right ŝ m₄))),
      q₆, hq₆, u1y₆, u1N₆, u1M₆, hu1₆,
      (awayLift (D.map t₆.right)
        ((D.map t₅.right).hom ((D.map t₄.right).hom (rAt k₁.right ŝ m₄))) _ rfl).hom
        ((awayLift (D.map t₅.right) ((D.map t₄.right).hom (rAt k₁.right ŝ m₄)) _ rfl).hom
          ((awayLift (D.map t₄.right) (rAt k₁.right ŝ m₄) _ rfl).hom u2z₃)), hu2₆,
      fun a ha ↦ he2₆ a ha, he3₆⟩
  refine ⟨k₆, t₁ ≫ t₂ ≫ t₃ ≫ t₄ ≫ t₅ ≫ t₆, ?_⟩
  exact ⟨heq.symm ▸ P6⟩

end Descent

section Assemble

variable {S A : CommRingCat.{u}} {s : D ⟶ (Functor.const J).obj S} {g : S ⟶ A}

/-- Stage representatives for finitely many elements of the colimit. -/
private lemma pushCocone_exists_rep_family (hs : IsColimit (Cocone.mk S s)) {j₀ : J}
    {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀} {v₀ : A₀ ⟶ A}
    (hpo : IsPushout (s.app j₀) f₀ g v₀) (n : ℕ) (x : Fin n → A) :
    ∃ (k : Under j₀) (y : Fin n → (pushSystem j₀ f₀).obj k),
      ∀ i, ((pushCocone hs hpo).ι.app k).hom (y i) = x i := by
  induction n with
  | zero => exact ⟨Under.mk (𝟙 j₀), Fin.elim0, fun i ↦ i.elim0⟩
  | succ m ih =>
      obtain ⟨k₁, y₁, hy₁⟩ := ih (fun i ↦ x i.castSucc)
      obtain ⟨k₂, y₂, hy₂⟩ := Concrete.isColimit_exists_rep _
        (isColimitPushCocone hs hpo) (x (Fin.last m))
      refine ⟨IsFiltered.max k₁ k₂, Fin.lastCases
        (((pushSystem j₀ f₀).map (IsFiltered.rightToMax k₁ k₂)).hom y₂)
        (fun i ↦ ((pushSystem j₀ f₀).map (IsFiltered.leftToMax k₁ k₂)).hom (y₁ i)), ?_⟩
      intro i
      refine Fin.lastCases ?_ (fun i ↦ ?_) i
      · simp only [Fin.lastCases_last]
        exact (pushCocone_w_apply hs hpo (IsFiltered.rightToMax k₁ k₂) y₂).trans hy₂
      · simp only [Fin.lastCases_castSucc]
        exact (pushCocone_w_apply hs hpo (IsFiltered.leftToMax k₁ k₂) (y₁ i)).trans (hy₁ i)

/-- Descend the piece data for all the elements of a finite cover. -/
private lemma exists_pieceAt_family (hs : IsColimit (Cocone.mk S s)) {j₀ : J}
    {A₀ : CommRingCat.{u}} {f₀ : D.obj j₀ ⟶ A₀} {v₀ : A₀ ⟶ A}
    (hpo : IsPushout (s.app j₀) f₀ g v₀)
    (hfp : MorphismProperty.isFinitelyPresentable.{u} CommRingCat.{u} f₀)
    (gens : Finset A₀) (n : ℕ)
    {k₀ : Under j₀} (ĝ : Fin n → (pushSystem j₀ f₀).obj k₀) (gA : Fin n → A)
    (himg : ∀ i, ((pushCocone hs hpo).ι.app k₀).hom (ĝ i) = gA i)
    (hstd : ∀ i, (letI : Algebra S A := g.hom.toAlgebra
      Algebra.IsStandardOpenImmersion S (Localization.Away (gA i)))) :
    ∃ (k : Under j₀) (t : k₀ ⟶ k), ∀ i,
      Nonempty (PieceAt j₀ f₀ gens k (((pushSystem j₀ f₀).map t).hom (ĝ i))) := by
  induction n with
  | zero => exact ⟨k₀, 𝟙 k₀, fun i ↦ i.elim0⟩
  | succ m ih =>
      obtain ⟨k₁, t₁, h₁⟩ := ih (fun i ↦ ĝ i.castSucc) (fun i ↦ gA i.castSucc)
        (fun i ↦ himg i.castSucc) (fun i ↦ hstd i.castSucc)
      have himg₁ : ((pushCocone hs hpo).ι.app k₁).hom
          (((pushSystem j₀ f₀).map t₁).hom (ĝ (Fin.last m))) = gA (Fin.last m) :=
        (pushCocone_w_apply hs hpo t₁ (ĝ (Fin.last m))).trans (himg (Fin.last m))
      obtain ⟨k₂, t₂, hP⟩ := exists_pieceAt hs hpo hfp gens
        (((pushSystem j₀ f₀).map t₁).hom (ĝ (Fin.last m))) (gA (Fin.last m)) himg₁
        (hstd (Fin.last m))
      refine ⟨k₂, t₁ ≫ t₂, ?_⟩
      have hcomp : ∀ x : (pushSystem j₀ f₀).obj k₀,
          ((pushSystem j₀ f₀).map (t₁ ≫ t₂)).hom x =
          ((pushSystem j₀ f₀).map t₂).hom (((pushSystem j₀ f₀).map t₁).hom x) := by
        intro x
        rw [Functor.map_comp]
        rfl
      intro i
      refine Fin.lastCases ?_ (fun i ↦ ?_) i
      · rw [hcomp]
        exact hP
      · rw [hcomp]
        obtain ⟨P⟩ := h₁ i
        exact ⟨P.push t₂⟩

/-- The key spreading result: if the pushout of an étale morphism along a filtered colimit
is a local isomorphism, then at some finite stage the pushout is already a local
isomorphism. -/
private lemma exists_isPushout_isLocalIso (hs : IsColimit (Cocone.mk S s)) {g : S ⟶ A}
    (hg : g.hom.IsLocalIso) {j₀ : J} {A₀ : CommRingCat.{u}}
    {f₀ : D.obj j₀ ⟶ A₀} {v₀ : A₀ ⟶ A} (hpo : IsPushout (s.app j₀) f₀ g v₀)
    (hf₀ : CommRingCat.etale f₀) :
    ∃ (j₁ : J) (A₁ : CommRingCat.{u}) (f₁ : D.obj j₁ ⟶ A₁) (v₁ : A₁ ⟶ A),
      IsPushout (s.app j₁) f₁ g v₁ ∧ f₁.hom.IsLocalIso := by
  classical
  -- generators of `A₀`
  have hfpres : f₀.hom.FinitePresentation := hf₀.2
  have hftype : (letI := f₀.hom.toAlgebra; Algebra.FiniteType (D.obj j₀) A₀) := by
    letI := f₀.hom.toAlgebra
    have : Algebra.FinitePresentation (D.obj j₀) A₀ := hfpres
    infer_instance
  obtain ⟨gens, hgens⟩ := (letI := f₀.hom.toAlgebra; hftype.out)
  have hfp : MorphismProperty.isFinitelyPresentable.{u} CommRingCat.{u} f₀ :=
    CommRingCat.isFinitelyPresentable_hom f₀ hfpres
  -- the cover data of the local isomorphism
  letI : Algebra S A := g.hom.toAlgebra
  have hLI : Algebra.IsLocalIso S A := hg
  have hspan := Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top S A
  have hone : (1 : A) ∈ Ideal.span
      {x : A | Algebra.IsStandardOpenImmersion S (Localization.Away x)} :=
    hspan ▸ Submodule.mem_top
  obtain ⟨n, cf, gf, hsum⟩ := Submodule.mem_span_set'.mp hone
  -- stage representatives for the cover and the coefficients
  obtain ⟨kr, yr, hyr⟩ := pushCocone_exists_rep_family hs hpo (n + n)
    (Fin.append cf (fun i ↦ (gf i : A)))
  set ĉ : Fin n → (pushSystem j₀ f₀).obj kr := fun i ↦ yr (Fin.castAdd n i) with hĉ
  set ĝr : Fin n → (pushSystem j₀ f₀).obj kr := fun i ↦ yr (Fin.natAdd n i) with hĝr
  have hĉimg : ∀ i, ((pushCocone hs hpo).ι.app kr).hom (ĉ i) = cf i := by
    intro i
    rw [hĉ]
    refine (hyr (Fin.castAdd n i)).trans ?_
    exact Fin.append_left cf _ i
  have hĝrimg : ∀ i, ((pushCocone hs hpo).ι.app kr).hom (ĝr i) = (gf i : A) := by
    intro i
    rw [hĝr]
    refine (hyr (Fin.natAdd n i)).trans ?_
    exact Fin.append_right cf _ i
  -- descend the cover equation
  have hcoveq : ((pushCocone hs hpo).ι.app kr).hom (∑ i, ĉ i * ĝr i) =
      ((pushCocone hs hpo).ι.app kr).hom 1 := by
    rw [map_sum, map_one]
    calc ∑ i, ((pushCocone hs hpo).ι.app kr).hom (ĉ i * ĝr i)
        = ∑ i, cf i * (gf i : A) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [map_mul, hĉimg, hĝrimg]
      _ = 1 := by
          rw [← hsum]
          exact Finset.sum_congr rfl fun i _ ↦ (smul_eq_mul ..).symm
  obtain ⟨kc, tc, htc⟩ := (IsColimit.eq_iff' (isColimitPushCocone hs hpo) _ _).mp hcoveq
  -- descend the piece data
  have himgc : ∀ i, ((pushCocone hs hpo).ι.app kc).hom
      (((pushSystem j₀ f₀).map tc).hom (ĝr i)) = (gf i : A) :=
    fun i ↦ (pushCocone_w_apply hs hpo tc (ĝr i)).trans (hĝrimg i)
  obtain ⟨kf, tf, hPf⟩ := exists_pieceAt_family hs hpo hfp gens n
    (fun i ↦ ((pushSystem j₀ f₀).map tc).hom (ĝr i)) (fun i ↦ (gf i : A)) himgc
    (fun i ↦ (gf i).2)
  -- the final stage and its elements
  set ĝf : Fin n → (pushSystem j₀ f₀).obj kf := fun i ↦
    ((pushSystem j₀ f₀).map tf).hom (((pushSystem j₀ f₀).map tc).hom (ĝr i)) with hĝf
  set ĉf : Fin n → (pushSystem j₀ f₀).obj kf := fun i ↦
    ((pushSystem j₀ f₀).map tf).hom (((pushSystem j₀ f₀).map tc).hom (ĉ i)) with hĉf
  have hcovf : (∑ i, ĉf i * ĝf i) = 1 := by
    have h1 := congrArg ((pushSystem j₀ f₀).map tf).hom htc
    rw [map_sum, map_sum, map_one, map_one] at h1
    calc ∑ i, ĉf i * ĝf i
        = ∑ i, ((pushSystem j₀ f₀).map tf).hom
            (((pushSystem j₀ f₀).map tc).hom (ĉ i * ĝr i)) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hĉf, hĝf, map_mul, map_mul]
      _ = 1 := h1
  -- each piece is a standard open immersion at the final stage
  letI : Algebra (D.obj kf.right) ((pushSystem j₀ f₀).obj kf) :=
    (pushInl j₀ f₀ kf).hom.toAlgebra
  have hstdf : ∀ i, Algebra.IsStandardOpenImmersion (D.obj kf.right)
      (Localization.Away (ĝf i)) := by
    intro i
    obtain ⟨P⟩ := hPf i
    have h := P.isStandardOpenImmersion hgens
    rw [← RingHom.isStandardOpenImmersion_algebraMap]
    exact h
  have hLIf : Algebra.IsLocalIso (D.obj kf.right) ((pushSystem j₀ f₀).obj kf) := by
    rw [Algebra.IsLocalIso.iff_span_isStandardOpenImmersion_eq_top]
    rw [Ideal.eq_top_iff_one]
    rw [← hcovf]
    refine Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span (hstdf i))
  refine ⟨kf.right, (pushSystem j₀ f₀).obj kf, pushInl j₀ f₀ kf,
    (pushCocone hs hpo).ι.app kf, pushSquare_stage hs hpo kf, hLIf⟩

/-- Assemble: given a pushout presentation of `g` at a stage by a local isomorphism, the
composition of an ind-Zariski morphism with `g` is a filtered colimit of local
isomorphisms. -/
private lemma ind_isLocalIso_of_isPushout {R : CommRingCat.{u}} {f : R ⟶ S}
    {tn : (Functor.const J).obj R ⟶ D} (hs : IsColimit (Cocone.mk S s))
    (hts : ∀ j, (RingHom.toMorphismProperty RingHom.IsLocalIso) (tn.app j) ∧
      tn.app j ≫ s.app j = f)
    {j₁ : J} {A₁ : CommRingCat.{u}} {f₁ : D.obj j₁ ⟶ A₁} {v₁ : A₁ ⟶ A}
    (hpo : IsPushout (s.app j₁) f₁ g v₁) (hf₁ : f₁.hom.IsLocalIso) :
    MorphismProperty.ind.{u} (RingHom.toMorphismProperty RingHom.IsLocalIso) (f ≫ g) := by
  refine ⟨Under j₁, inferInstance, inferInstance, pushSystem j₁ f₁,
    { app := fun k ↦ tn.app k.right ≫ pushInl j₁ f₁ k
      naturality := fun k l u ↦ ?_ }, (pushCocone hs hpo).ι, isColimitPushCocone hs hpo,
    fun k ↦ ⟨?_, ?_⟩⟩
  · have h2 : tn.app k.right ≫ D.map u.right = tn.app l.right := by
      have := tn.naturality u.right
      simpa using this.symm
    have h3 : (tn.app k.right ≫ pushInl j₁ f₁ k) ≫ (pushSystem j₁ f₁).map u =
        tn.app l.right ≫ pushInl j₁ f₁ l := by
      rw [Category.assoc, pushInl_map j₁ f₁ u, ← Category.assoc, h2]
    have h1 : ((Functor.const (Under j₁)).obj R).map u = 𝟙 R := rfl
    rw [h1]
    exact (Category.id_comp _).trans h3.symm
  · change ((tn.app k.right ≫ pushInl j₁ f₁ k)).hom.IsLocalIso
    rw [CommRingCat.hom_comp]
    refine RingHom.IsLocalIso.comp ?_ (hts k.right).1
    have hcb : (RingHom.toMorphismProperty RingHom.IsLocalIso) (pushInl j₁ f₁ k) :=
      MorphismProperty.IsStableUnderCobaseChange.of_isPushout (pushSquare j₁ f₁ k) hf₁
    exact hcb
  · change (tn.app k.right ≫ pushInl j₁ f₁ k) ≫ (pushCocone hs hpo).ι.app k = f ≫ g
    refine (Category.assoc _ _ _).trans ?_
    rw [pushInl_cocone hs hpo k]
    refine (Category.assoc _ _ _).symm.trans ?_
    rw [(hts k.right).2]

end Assemble

end PieceSpread

/-- The composition of an ind-Zariski ring homomorphism with a local isomorphism is
ind-Zariski. This is the key step in the proof that ind-Zariski ring homomorphisms are
stable under composition. -/
theorem comp_isLocalIso {X Y Z : Type u} [CommRing X] [CommRing Y] [CommRing Z]
    {f : X →+* Y} {t : Y →+* Z} (ht : t.IsLocalIso) (hf : f.IndZariski) :
    (t.comp f).IndZariski := by
  rw [iff_ind_isLocalIso] at hf ⊢
  rw [CommRingCat.ofHom_comp]
  obtain ⟨J, _, _, D, tn, s, hs, hts⟩ := hf
  have htE : CommRingCat.etale (CommRingCat.ofHom t) := by
    change t.Etale
    algebraize [t]
    have h1 : Algebra.IsLocalIso Y Z := ht
    have h2 := Algebra.IsLocalIso.etale Y Z
    rw [← t.algebraMap_toAlgebra]
    exact RingHom.etale_algebraMap.mpr h2
  obtain ⟨j₀, A₀, f₀, v₀, hpo, hf₀⟩ :=
    CommRingCat.etale.exists_isPushout_of_isFiltered hs (CommRingCat.ofHom t) htE
  obtain ⟨j₁, A₁, f₁, v₁, hpo₁, hf₁⟩ := exists_isPushout_isLocalIso hs
    (show (CommRingCat.ofHom t).hom.IsLocalIso from ht) hpo hf₀
  exact ind_isLocalIso_of_isPushout hs hts hpo₁ hf₁

variable {f : R →+* S} {g : S →+* T}

lemma comp (hg : g.IndZariski) (hf : f.IndZariski) : (g.comp f).IndZariski := by
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := (iff_ind_isLocalIso g).mp hg
  refine (iff_ind_indZariski (g.comp f)).mpr ?_
  rw [CommRingCat.ofHom_comp]
  refine ⟨J, ‹_›, ‹_›, D, (Functor.const J).map (CommRingCat.ofHom f) ≫ t, s, hs,
    fun j ↦ ⟨?_, ?_⟩⟩
  · change ((CommRingCat.ofHom f) ≫ t.app j).hom.IndZariski
    rw [CommRingCat.hom_comp]
    exact RingHom.IndZariski.comp_isLocalIso (hts j).1 hf
  · simp only [NatTrans.comp_app, Functor.const_obj_obj, Functor.const_map_app,
      Category.assoc]
    exact whisker_eq (CommRingCat.ofHom f) (hts j).2

lemma prod {g : R →+* T} (hf : f.IndZariski) (hg : g.IndZariski) : (f.prod g).IndZariski := by
  algebraize [f, g]
  exact Algebra.IndZariski.prod R S T

lemma pi {ι : Type u} [_root_.Finite ι] (S : ι → Type u) [∀ i, CommRing (S i)]
    (f : ∀ i, R →+* (S i)) (hf : ∀ i, (f i).IndZariski) : (Pi.ringHom f).IndZariski := by
  let (i : ι) : Algebra R (S i) := (f i).toAlgebra
  have (i : ι) : Algebra.IndZariski R (S i) := hf i
  exact Algebra.IndZariski.pi R S

lemma flat (h : f.IndZariski) : f.Flat := by
  algebraize [f]
  exact .of_indZariski R S

@[stacks 096T]
theorem bijectiveOnStalks (h : f.IndZariski) : f.BijectiveOnStalks := by
  algebraize [f]
  exact Algebra.IndZariski.bijectiveOnStalks_algebraMap R S

/-- A ring hom is ind-Zariski if it can be written as a filtered colimit of ind-Zariski maps. -/
lemma of_isColimit {R S : CommRingCat.{u}} (f : R ⟶ S) (J : Type u) [SmallCategory J]
    [IsFiltered J] (D : J ⥤ CommRingCat.{u}) {t : (Functor.const J).obj R ⟶ D}
    {c : D ⟶ (Functor.const J).obj S} (hc : IsColimit (.mk _ c))
    (htc : ∀ i, (t.app i).hom.IndZariski ∧ t.app i ≫ c.app i = f) : f.hom.IndZariski :=
  (iff_ind_indZariski _).mpr ⟨J, ‹_›, ‹_›, D, t, c, hc, by simpa using htc⟩

theorem _root_.Algebra.IndZariski.iff_ind_indZariksi [Algebra R S] :
    Algebra.IndZariski R S ↔ ObjectProperty.ind.{u}
      (RingHom.toObjectProperty RingHom.IndZariski R) (.of R S) :=
  (algebraMap_iff (R := R) (S := S)).symm.trans
    ((iff_ind_indZariski _).trans
      respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty)

end RingHom.IndZariski

namespace Algebra.IndZariski

@[stacks 096Q]
lemma trans [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.IndZariski R S] [Algebra.IndZariski S T] :
    Algebra.IndZariski R T := by
  rw [← RingHom.IndZariski.algebraMap_iff R T, IsScalarTower.algebraMap_eq R S T]
  exact RingHom.IndZariski.comp
    ((RingHom.IndZariski.algebraMap_iff S T).mpr ‹_›)
    ((RingHom.IndZariski.algebraMap_iff R S).mpr ‹_›)

end Algebra.IndZariski

end RingHom
