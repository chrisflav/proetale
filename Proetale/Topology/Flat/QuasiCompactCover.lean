/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Topology.Flat.CompactOpenCovered
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib

/-!
# Quasi-compact covers

A cover of a scheme is quasi-compact if every affine open of the base can be covered
by a finite union of images of quasi-compact opens of the components.

This is used to define the fpqc (faithfully flat, quasi-compact) topology, where covers are given by
flat covers that are quasi-compact.
-/

universe w u v

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry.Scheme.Cover

variable {P : MorphismProperty Scheme.{u}} {S : Scheme.{u}}

/--
A cover of a scheme is quasi-compact if every affine open of the base can be covered
by a finite union of images of quasi-compact opens of the components.
-/
@[stacks 022B]
class QuasiCompact (𝒰 : S.Cover P) : Prop where
  isCompactOpenCovered_of_isAffineOpen {U : S.Opens} (hU : IsAffineOpen U) :
    IsCompactOpenCovered (fun i ↦ (𝒰.map i).base) U.1

lemma IsAffineOpen.isCompactOpenCovered (𝒰 : S.Cover P) [QuasiCompact 𝒰]
    {U : S.Opens} (hU : IsAffineOpen U) :
    IsCompactOpenCovered (fun i ↦ (𝒰.map i).base) U.1 :=
  QuasiCompact.isCompactOpenCovered_of_isAffineOpen hU

namespace QuasiCompact

variable {𝒰 : S.Cover P}

open TopologicalSpace.Opens

variable (𝒰) in
lemma exists_isAffineOpen_of_isCompact [𝒰.QuasiCompact] {U : S.Opens} (hU : IsCompact U.1) :
    ∃ (n : ℕ) (f : Fin n → 𝒰.J) (V : ∀ i, (𝒰.obj (f i)).Opens),
      (∀ i, IsAffineOpen (V i)) ∧
      ⋃ i, (𝒰.map (f i)).base '' (V i) = U := by
  suffices h : IsCompactOpenCovered (fun i ↦ (𝒰.map i).base) U
  · obtain ⟨n, a, V, ha, _, heq⟩ := h.exists_mem_of_isBasis (fun i ↦ isBasis_affine_open (𝒰.obj i))
      (fun _ _ h ↦ h.isCompact)
    exact ⟨n, a, V, ha, heq⟩
  obtain ⟨Us, hUs, hUf, hUc⟩ := (isBasis_affine_open S).exists_finite_of_isCompact hU
  refine .of_iUnion_eq_of_finite (SetLike.coe '' Us) (by aesop) (hUf.image _) ?_
  simpa using fun t ht ↦ IsAffineOpen.isCompactOpenCovered 𝒰 (hUs ht)

/-- If the component maps of `𝒰` are open, `𝒰` is quasi-compact. This in particular
applies if `P` is flat and locally of finite presentation (fppf) and hence in particular
for (weakly)-étale and open covers. -/
@[stacks 022C]
lemma of_isOpenMap (h : ∀ i, IsOpenMap (𝒰.map i).base) :
    QuasiCompact 𝒰 where
  isCompactOpenCovered_of_isAffineOpen {U} hU := .of_isOpenMap (fun i ↦ isBasis_affine_open (𝒰.obj i))
    (fun _ _ h ↦ h.isCompact) (fun i ↦ (𝒰.map i).continuous) h
    (fun x _ ↦ ⟨𝒰.f x, 𝒰.covers x⟩) U.2 hU.isCompact

instance (𝒰 : S.OpenCover) : 𝒰.QuasiCompact :=
  of_isOpenMap fun i ↦ (𝒰.map i).isOpenEmbedding.isOpenMap

end AlgebraicGeometry.Scheme.Cover.QuasiCompact
