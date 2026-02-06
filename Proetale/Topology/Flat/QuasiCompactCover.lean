/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Cover.Sigma
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Proetale.Topology.Flat.CompactOpenCovered
import Proetale.Mathlib.AlgebraicGeometry.Morphisms.Basic
import Proetale.Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Proetale.Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Upstreamer

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

variable {P : MorphismProperty Scheme.{u}} {S : Scheme.{u}}

variable (𝒰 : Scheme.Cover.{v} (precoverage P) S)

namespace Scheme.Cover.QuasiCompact

variable {𝒰 : Cover.{v} (Scheme.precoverage P) S}

open TopologicalSpace.Opens

open TopologicalSpace Opens

lemma iff_sigma {𝒰 : Cover.{u} (Scheme.precoverage P) S} [IsZariskiLocalAtSource P] :
    QuasiCompactCover 𝒰.toPreZeroHypercover ↔ QuasiCompactCover 𝒰.sigma.toPreZeroHypercover := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact .of_hom 𝒰.toSigma
  · refine ⟨fun {U} hU ↦ ?_⟩
    have := hU.isCompactOpenCovered 𝒰.sigma.toPreZeroHypercover
    rw [IsCompactOpenCovered.iff_isCompactOpenCovered_sigmaMk]
    rw [IsCompactOpenCovered.iff_of_unique] at this ⊢
    obtain ⟨V, hV, hU⟩ := this
    have heq : (fun a ↦ (𝒰.f a.1).base a.2) ∘ (sigmaMk 𝒰.X).symm = (𝒰.sigma.f ⟨⟩).base := by
      apply (Equiv.comp_symm_eq _ _ _).mpr
      ext ⟨i, y⟩
      simp [← Scheme.Hom.comp_apply]
    refine ⟨⟨(sigmaMk 𝒰.X).symm '' V.1, by simpa using V.2⟩, by simpa, ?_⟩
    simp only [sigma_I₀, PUnit.default_eq_unit, sigma_X, carrier_eq_coe, ← Set.image_comp]
    convert hU

lemma exists_hom [P.IsMultiplicative] {S : Scheme.{u}} (𝒰 : S.Cover (precoverage P))
    [P.RespectsLeft @IsOpenImmersion] [CompactSpace S] [QuasiCompactCover 𝒰.toPreZeroHypercover] :
    ∃ (𝒱 : Scheme.AffineCover.{w} P S) (f : 𝒱.cover ⟶ 𝒰),
      Finite 𝒱.I₀ ∧ ∀ j, IsOpenImmersion (f.h₀ j) := by
  obtain ⟨n, f, V, hV, h⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact 𝒰.1
    (show IsCompact (⊤ : Opens S).carrier from isCompact_univ)
  simp [← Set.univ_subset_iff, Set.subset_def] at h
  choose idx x hmem hx using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      { I₀ := ULift (Fin n)
        X i := Γ(_, V i.down)
        f i := (hV _).fromSpec ≫ 𝒰.f (f _)
        idx s := ⟨idx s⟩
        covers s := by
          use (hV _).isoSpec.hom.base ⟨x s, hmem s⟩
          rw [← Scheme.Hom.comp_apply, ← IsAffineOpen.isoSpec_inv_ι, Category.assoc,
            Iso.hom_inv_id_assoc]
          simp [hx]
        map_prop i :=
          RespectsLeft.precomp (Q := IsOpenImmersion) _ inferInstance _ (𝒰.map_prop _) }
  · exact
      { s₀ i := f i.down
        h₀ i := (hV i.down).fromSpec }
  · infer_instance
  · infer_instance

instance {S : Scheme.{u}} [IsAffine S] (𝒰 : S.AffineCover P) [Finite 𝒰.I₀] :
    QuasiCompactCover 𝒰.cover.toPreZeroHypercover :=
  sorry

end AlgebraicGeometry.Scheme.Cover.QuasiCompact
