/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Mathlib.Topology.Inseparable
import Proetale.Mathlib.Topology.Separation.Basic
import Proetale.Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.JacobsonSpace

/-!
# w-local spaces

In this file we define w-local spaces. These are spectral spaces in which every point
specializes to a unique closed point and where the set of closed points is closed.
-/

/--
A spectral space is w-local if every point specializes to a unique closed point
and the set of closed points is closed.
Note: In a spectral space, every point specializes to a closed point, so we only require
the uniqueness.
-/
class WLocalSpace (X : Type*) [TopologicalSpace X] : Prop extends SpectralSpace X where
  /-- Any two closed specializations of a point are equal. -/
  eq_of_specializes {x c c' : X} (hc : IsClosed {c}) (hc' : IsClosed {c'})
    (hxc : x ⤳ c) (hxc' : x ⤳ c') : c = c'
  /-- The set of closed points is closed. -/
  isClosed_closedPoints : IsClosed (closedPoints X)

attribute [instance] WLocalSpace.isClosed_closedPoints

/-- A w-local map is a spectral map that maps closed points to closed points. -/
@[mk_iff]
structure IsWLocalMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) : Prop
    extends IsSpectralMap f where
  closedPoints_subset_preimage_closedPoints : closedPoints X ⊆ f ⁻¹' (closedPoints Y)

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A w-local map sends closed points to closed points. -/
lemma IsWLocalMap.isClosed_singleton {f : X → Y} (hf : IsWLocalMap f)
    {x : X} (hx : IsClosed {x}) :
    IsClosed {f x} :=
  mem_closedPoints_iff.mp
    (hf.closedPoints_subset_preimage_closedPoints (mem_closedPoints_iff.mpr hx))

lemma IsWLocalMap.comp {Z : Type*} [TopologicalSpace Z] {f : X → Y} {g : Y → Z}
    (hf : IsWLocalMap f) (hg : IsWLocalMap g) :
    IsWLocalMap (g ∘ f) where
  toIsSpectralMap := hg.toIsSpectralMap.comp hf.toIsSpectralMap
  closedPoints_subset_preimage_closedPoints _ hx :=
    hg.closedPoints_subset_preimage_closedPoints
      (hf.closedPoints_subset_preimage_closedPoints hx)

/-- An embedding with specialization-stable range maps closed singletons to closed singletons. -/
lemma Topology.IsEmbedding.isClosed_singleton
    {f : X → Y} (hf : IsEmbedding f) (hrange : StableUnderSpecialization (Set.range f))
    {z : X} (hz : IsClosed {z}) :
    IsClosed {f z} := by
  rw [← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm (fun y hy => ?_) subset_closure
  have hspec : f z ⤳ y := specializes_iff_mem_closure.mpr hy
  obtain ⟨z', rfl⟩ := hrange hspec (Set.mem_range_self z)
  have hzz' : z ⤳ z' := hf.specializes_iff.mp hspec
  have : z' ∈ ({z} : Set X) := hz.closure_eq ▸ hzz'.mem_closure
  rw [Set.mem_singleton_iff.mp this]
  exact Set.mem_singleton _

/-- If `f` is an embedding and `{f z}` is closed, then `{z}` is closed. -/
lemma Topology.IsEmbedding.isClosed_singleton_of_isClosed_image_singleton
    {f : X → Y} (hf : IsEmbedding f) {z : X} (hz : IsClosed {f z}) :
    IsClosed {z} := by
  rw [← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm (fun x hx => ?_) subset_closure
  have hfspec : f z ⤳ f x := (specializes_iff_mem_closure.mpr hx).map hf.continuous
  exact Set.mem_singleton_iff.mpr
    (hf.injective (Set.mem_singleton_iff.mp (hz.closure_eq ▸ hfspec.mem_closure)))

/-- An embedding with specialization-stable range identifies
closed points of `X` with the preimage of closed points of `Y`. -/
lemma Topology.IsEmbedding.closedPoints_eq_preimage
    {f : X → Y} (hf : IsEmbedding f) (hrange : StableUnderSpecialization (Set.range f)) :
    closedPoints X = f ⁻¹' closedPoints Y := by
  ext x
  simp only [Set.mem_preimage, mem_closedPoints_iff]
  exact ⟨hf.isClosed_singleton hrange, hf.isClosed_singleton_of_isClosed_image_singleton⟩

lemma Topology.IsEmbedding.wLocalSpace_of_stableUnderSpecialization_range {f : X → Y}
    (hf : IsEmbedding f) (h : StableUnderSpecialization (Set.range f))
    [SpectralSpace X] [WLocalSpace Y] : WLocalSpace X where
  eq_of_specializes {x c c'} hc hc' hxc hxc' :=
    hf.injective (WLocalSpace.eq_of_specializes (hf.isClosed_singleton h hc)
      (hf.isClosed_singleton h hc') (hxc.map hf.continuous) (hxc'.map hf.continuous))
  isClosed_closedPoints := by
    rw [hf.closedPoints_eq_preimage h]
    exact WLocalSpace.isClosed_closedPoints.preimage hf.continuous

lemma StableUnderSpecialization.generalizationHull_of_wLocalSpace [WLocalSpace X] {s : Set X}
    (hs : StableUnderSpecialization s) :
    StableUnderSpecialization (generalizationHull s) := by
  rw [generalizationHull_eq]
  intro a b hab ha
  obtain ⟨y, hys, hay⟩ := ha
  obtain ⟨c, hc_closed, hyc⟩ := exists_isClosed_specializes y
  obtain ⟨c', hc'_closed, hbc'⟩ := exists_isClosed_specializes b
  obtain rfl := WLocalSpace.eq_of_specializes hc_closed hc'_closed
    (hay.trans hyc) (hab.trans hbc')
  exact ⟨c, hs hyc hys, hbc'⟩

lemma Topology.IsClosedEmbedding.wLocalSpace {f : X → Y} (hf : IsClosedEmbedding f)
    [WLocalSpace Y] : WLocalSpace X :=
  have : SpectralSpace X := hf.spectralSpace
  hf.isEmbedding.wLocalSpace_of_stableUnderSpecialization_range
    hf.isClosedMap.isClosed_range.stableUnderSpecialization

lemma isClosed_generalizationHull_of_wLocalSpace [WLocalSpace X] {s : Set X} (hs : IsClosed s) :
    IsClosed (generalizationHull s) :=
  sorry

/-- If `X` is w-local, the composition `closedPoints X → X → ConnectedComponents X` is
a homeomorphism. -/
lemma WLocalSpace.isHomeomorph_connectedComponents_closedPoints (X : Type*) [TopologicalSpace X]
    [WLocalSpace X] :
    IsHomeomorph (ConnectedComponents.mk ∘ ((↑) : closedPoints X → X)) :=
  sorry

/-- The closed points of a w-local space are homeomorphic to the connected components. -/
noncomputable
def WLocalSpace.closedPointsHomeomorph {X : Type*} [TopologicalSpace X] [WLocalSpace X] :
    closedPoints X ≃ₜ ConnectedComponents X :=
  (WLocalSpace.isHomeomorph_connectedComponents_closedPoints X).homeomorph
