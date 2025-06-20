/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Cover.Sigma
import Proetale.Topology.Flat.CompactOpenCovered
import Proetale.Mathlib.AlgebraicGeometry.Morphisms.Basic
import Proetale.Mathlib.AlgebraicGeometry.Cover.MorphismProperty

/-!
# Quasi-compact covers

A cover of a scheme is quasi-compact if every affine open of the base can be covered
by a finite union of images of quasi-compact opens of the components.

This is used to define the fpqc (faithfully flat, quasi-compact) topology, where covers are given by
flat covers that are quasi-compact.
-/

universe w u v

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [QuasiCompact f] [CompactSpace Y] : CompactSpace ↑(pullback f g) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.snd _ _)

instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [QuasiCompact g] [CompactSpace X] : CompactSpace ↑(pullback f g) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.fst _ _)

lemma IsAffineOpen.isCompact_pullback_inf {X Y Z : Scheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsCompact V.1)
    {W : Z.Opens} (hW : IsAffineOpen W) (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ g ⁻¹ᵁ W) :
    IsCompact (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V).1 := by
  have : IsAffine U.toScheme := hU
  have : IsAffine W.toScheme := hW
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV
  let f' : U.toScheme ⟶ W := f.resLE _ _ hUW
  let q : Scheme.Opens.toScheme V ⟶ W :=
    IsOpenImmersion.lift W.ι (Scheme.Opens.ι _ ≫ g) <| by simpa [Set.range_comp]
  let p : pullback f' q ⟶ pullback f g :=
    pullback.map _ _ _ _ U.ι (Scheme.Opens.ι _) W.ι (by simp [f']) (by simp [q])
  convert isCompact_range p.continuous
  simp [p, Scheme.Pullback.range_map]

variable {P : MorphismProperty Scheme.{u}} {S : Scheme.{u}}

/--
A cover of a scheme is quasi-compact if every affine open of the base can be covered
by a finite union of images of quasi-compact opens of the components.
-/
@[stacks 022B, mk_iff]
class Scheme.Cover.QuasiCompact (𝒰 : Cover.{v} P S) : Prop where
  isCompactOpenCovered_of_isAffineOpen {U : S.Opens} (hU : IsAffineOpen U) :
    IsCompactOpenCovered (fun i ↦ (𝒰.map i).base) U.1

variable (𝒰 : Scheme.Cover.{v} P S)

lemma IsAffineOpen.isCompactOpenCovered (𝒰 : S.Cover P) [𝒰.QuasiCompact]
    {U : S.Opens} (hU : IsAffineOpen U) :
    IsCompactOpenCovered (fun i ↦ (𝒰.map i).base) U.1 :=
  Scheme.Cover.QuasiCompact.isCompactOpenCovered_of_isAffineOpen hU

lemma Scheme.Cover.isCompactOpenCovered_of_isCompact (𝒰 : S.Cover P) [𝒰.QuasiCompact]
    {U : S.Opens} (hU : IsCompact U.1) :
    IsCompactOpenCovered (fun i ↦ (𝒰.map i).base) U.1 := by
  obtain ⟨Us, hUs, hUf, hUc⟩ := (isBasis_affine_open S).exists_finite_of_isCompact hU
  refine .of_iUnion_eq_of_finite (SetLike.coe '' Us) (by aesop) (hUf.image _) ?_
  simpa using fun t ht ↦ IsAffineOpen.isCompactOpenCovered 𝒰 (hUs ht)

namespace Scheme.Cover.QuasiCompact

variable {𝒰 : Cover.{v} P S}

open TopologicalSpace.Opens

@[simp]
lemma weaken_iff {Q : MorphismProperty Scheme.{u}} (hPQ : P ≤ Q) {𝒰 : Cover.{v} P S} :
    (𝒰.weaken hPQ).QuasiCompact ↔ 𝒰.QuasiCompact := by
  simp_rw [quasiCompact_iff]

variable (𝒰) in
lemma exists_isAffineOpen_of_isCompact [𝒰.QuasiCompact] {U : S.Opens} (hU : IsCompact U.1) :
    ∃ (n : ℕ) (f : Fin n → 𝒰.J) (V : ∀ i, (𝒰.obj (f i)).Opens),
      (∀ i, IsAffineOpen (V i)) ∧
      ⋃ i, (𝒰.map (f i)).base '' (V i) = U := by
  obtain ⟨n, a, V, ha, heq⟩ := (𝒰.isCompactOpenCovered_of_isCompact hU).exists_mem_of_isBasis
    (fun i ↦ isBasis_affine_open (𝒰.obj i)) (fun _ _ h ↦ h.isCompact)
  exact ⟨n, a, V, ha, heq⟩

/-- If the component maps of `𝒰` are open, `𝒰` is quasi-compact. This in particular
applies if `P` is flat and locally of finite presentation (fppf) and hence in particular
for (weakly)-étale and open covers. -/
@[stacks 022C]
lemma of_isOpenMap (h : ∀ i, IsOpenMap (𝒰.map i).base) :
    QuasiCompact 𝒰 where
  isCompactOpenCovered_of_isAffineOpen {U} hU := .of_isOpenMap
    (fun i ↦ (𝒰.map i).continuous) h (fun x _ ↦ ⟨𝒰.f x, 𝒰.covers x⟩) U.2 hU.isCompact

instance (𝒰 : S.OpenCover) : 𝒰.QuasiCompact :=
  of_isOpenMap fun i ↦ (𝒰.map i).isOpenEmbedding.isOpenMap

open TopologicalSpace Opens

instance [P.IsStableUnderBaseChange] (𝒰 : S.Cover P) [𝒰.QuasiCompact] {T : Scheme.{u}} (f : T ⟶ S) :
    (𝒰.pullbackCover f).QuasiCompact := by
  refine ⟨fun {U'} hU' ↦ ?_⟩
  wlog h : ∃ (U : S.Opens), IsAffineOpen U ∧ f.base '' U' ⊆ U generalizing U'
  · refine .of_isCompact_of_forall_exists hU'.isCompact fun x hxU ↦ ?_
    obtain ⟨W, hW, hx, _⟩ := isBasis_iff_nbhd.mp (isBasis_affine_open S) (mem_top (f.base x))
    obtain ⟨W', hW', hx', hle⟩ := isBasis_iff_nbhd.mp (isBasis_affine_open T)
      (show x ∈ f ⁻¹ᵁ W ⊓ U' from ⟨hx, hxU⟩)
    refine ⟨W', le_trans hle inf_le_right, by simpa [hx], W'.2, ?_⟩
    exact this hW' ⟨W, hW, by simpa using le_trans hle inf_le_left⟩
  obtain ⟨U, hU, hsub⟩ := h
  obtain ⟨s, hf, V, hc, (heq : _ = (U : Set S))⟩ := hU.isCompactOpenCovered 𝒰
  refine ⟨s, hf, fun i hi ↦ pullback.fst f (𝒰.map i) ⁻¹ᵁ U' ⊓ pullback.snd f (𝒰.map i) ⁻¹ᵁ (V i hi),
      fun i hi ↦ ?_, ?_⟩
  · exact hU'.isCompact_pullback_inf (hc _ _) hU (by simpa using hsub) <| show _ ⊆ _ by
      simpa [← heq, Set.range_comp] using Set.subset_iUnion_of_subset i
        (Set.subset_iUnion_of_subset hi (Set.subset_preimage_image _ _))
  · refine subset_antisymm (by simp) (fun x hx ↦ ?_)
    have : f.base x ∈ (U : Set S) := hsub ⟨x, hx, rfl⟩
    simp_rw [← heq, Set.mem_iUnion] at this
    obtain ⟨i, hi, y, hy, heq⟩ := this
    simp_rw [Set.mem_iUnion]
    obtain ⟨z, hzl, hzr⟩ := Pullback.exists_preimage_pullback x y heq.symm
    refine ⟨i, hi, z, ⟨by simpa [hzl], by simpa [hzr]⟩, hzl⟩

instance [P.IsStableUnderBaseChange] (𝒰 : S.Cover P) [𝒰.QuasiCompact] {T : Scheme.{u}} (f : T ⟶ S) :
    (𝒰.pullbackCover' f).QuasiCompact := by
  sorry

/-- If `𝒱` is a refinement of `𝒰` such that `𝒱` is quasicompact, also `𝒰` is quasicompact. -/
@[stacks 03L8]
lemma of_hom [P.IsMultiplicative] {𝒰 𝒱 : S.Cover P} (f : 𝒱 ⟶ 𝒰) [𝒱.QuasiCompact] :
    𝒰.QuasiCompact := by
  refine ⟨fun {U} hU ↦ ?_⟩
  exact .of_comp (a := f.idx) (fun i ↦ (𝒱.map i).base) (fun i ↦ (f.app i).base)
    (fun _ ↦ Hom.continuous _) (fun i ↦ funext <| by simp [← Scheme.comp_base_apply])
    (fun _ ↦ Hom.continuous _) U.2 (hU.isCompactOpenCovered 𝒱)

lemma iff_sigma {𝒰 : Cover.{u} P S} [IsLocalAtSource P] :
    𝒰.QuasiCompact ↔ 𝒰.sigma.QuasiCompact := by
  wlog hP : P = ⊤
  · rw [← weaken_iff le_top (𝒰 := 𝒰), ← weaken_iff le_top (𝒰 := 𝒰.sigma)]
    exact this rfl
  subst hP
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← weaken_iff le_top] at *
    exact of_hom (𝒰.weaken le_top).toSigma
  · refine ⟨fun {U} hU ↦ ?_⟩
    have := hU.isCompactOpenCovered 𝒰.sigma
    rw [IsCompactOpenCovered.iff_isCompactOpenCovered_sigmaMk]
    rw [IsCompactOpenCovered.iff_of_unique] at this ⊢
    obtain ⟨V, hV, hU⟩ := this
    have heq : (fun a ↦ (𝒰.map a.1).base a.2) ∘ (sigmaMk 𝒰.obj).symm = (𝒰.sigma.map ⟨⟩).base := by
      apply (Equiv.comp_symm_eq _ _ _).mpr
      ext ⟨i, y⟩
      simp [← Scheme.comp_base_apply]
    refine ⟨⟨(sigmaMk 𝒰.obj).symm '' V.1, by simpa using V.2⟩, by simpa, ?_⟩
    simp only [sigma_J, PUnit.default_eq_unit, sigma_obj, carrier_eq_coe, ← Set.image_comp]
    convert hU

instance [P.ContainsIdentities] [P.RespectsIso] {X Y : Scheme.{u}} {f : X ⟶ Y} [IsIso f] :
    (coverOfIsIso (P := P) f).QuasiCompact :=
  of_isOpenMap (fun _ ↦ f.homeomorph.isOpenMap)

instance [P.IsStableUnderComposition] {X : Scheme.{u}} (𝒰 : Cover.{v} P X) [𝒰.QuasiCompact]
    (f : ∀ (x : 𝒰.J), (𝒰.obj x).Cover P) [∀ x, (f x).QuasiCompact] :
    QuasiCompact (𝒰.bind f) := by
  constructor
  intro U hU
  obtain ⟨s, hs, V, hcV, hU⟩ := hU.isCompactOpenCovered 𝒰
  have (i hi) : IsCompactOpenCovered (fun k ↦ ((f i).map k).base) (V i hi) :=
    (f i).isCompactOpenCovered_of_isCompact (hcV i hi)
  choose t ht W hcW hV using this
  have : Finite s := hs
  have (i hi) : Finite (t i hi) := ht i hi
  refine .of_finite (κ := Σ (i : s), t i.1 i.2) (fun p ↦ ⟨p.1, p.2⟩) (fun p ↦ W _ p.1.2 _ p.2.2)
    (fun p ↦ hcW ..) ?_
  simpa [← hV, Set.iUnion_sigma, Set.iUnion_subtype, Set.image_iUnion, Set.image_image] using hU

end AlgebraicGeometry.Scheme.Cover.QuasiCompact
