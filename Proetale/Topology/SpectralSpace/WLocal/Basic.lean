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
    {x : X} (hx : IsClosed ({x} : Set X)) :
    IsClosed ({f x} : Set Y) :=
  mem_closedPoints_iff.mp
    (hf.closedPoints_subset_preimage_closedPoints (mem_closedPoints_iff.mpr hx))

lemma IsWLocalMap.comp {Z : Type*} [TopologicalSpace Z] {f : X → Y} {g : Y → Z}
    (hf : IsWLocalMap f) (hg : IsWLocalMap g) :
    IsWLocalMap (g ∘ f) where
  toIsSpectralMap := hg.toIsSpectralMap.comp hf.toIsSpectralMap
  closedPoints_subset_preimage_closedPoints _ hx :=
    hg.closedPoints_subset_preimage_closedPoints
      (hf.closedPoints_subset_preimage_closedPoints hx)

/-- An embedding with specialization-stable range into a w-local space maps closed singletons
to closed singletons. -/
lemma Topology.IsEmbedding.isClosed_singleton_image
    {f : X → Y} (hf : IsEmbedding f) (hrange : StableUnderSpecialization (Set.range f))
    [WLocalSpace Y] {z : X} (hz : IsClosed ({z} : Set X)) :
    IsClosed ({f z} : Set Y) := by
  rw [← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm (fun y hy => ?_) subset_closure
  have hspec : f z ⤳ y := specializes_iff_mem_closure.mpr hy
  obtain ⟨z', rfl⟩ := hrange hspec (Set.mem_range_self z)
  have hzz' : z ⤳ z' := hf.specializes_iff.mp hspec
  have : z' ∈ ({z} : Set X) := hz.closure_eq ▸ hzz'.mem_closure
  rw [Set.mem_singleton_iff.mp this]
  exact Set.mem_singleton _

lemma Topology.IsEmbedding.wLocalSpace_of_stableUnderSpecialization_range {f : X → Y}
    (hf : IsEmbedding f) (h : StableUnderSpecialization (Set.range f))
    [SpectralSpace X] [WLocalSpace Y] : WLocalSpace X where
  eq_of_specializes {x c c'} hc hc' hxc hxc' :=
    hf.injective (WLocalSpace.eq_of_specializes (hf.isClosed_singleton_image h hc)
      (hf.isClosed_singleton_image h hc') (hxc.map hf.continuous) (hxc'.map hf.continuous))
  isClosed_closedPoints := by
    have : closedPoints X = f ⁻¹' closedPoints Y := by
      ext x
      simp only [Set.mem_preimage, mem_closedPoints_iff]
      exact ⟨hf.isClosed_singleton_image h, fun hfx => by
        rw [← closure_eq_iff_isClosed]
        refine Set.Subset.antisymm (fun x' hx' => ?_) subset_closure
        have hspec : x ⤳ x' := specializes_iff_mem_closure.mpr hx'
        have hfspec : f x ⤳ f x' := hspec.map hf.continuous
        have hmem : f x' ∈ ({f x} : Set Y) := hfx.closure_eq ▸ hfspec.mem_closure
        exact Set.mem_singleton_iff.mpr (hf.injective (Set.mem_singleton_iff.mp hmem))⟩
    rw [this]
    exact WLocalSpace.isClosed_closedPoints.preimage hf.continuous

lemma StableUnderSpecialization.generalizationHull_of_wLocalSpace [WLocalSpace X] {s : Set X}
    (hs : StableUnderSpecialization s) :
    StableUnderSpecialization (generalizationHull s) := by
  rw [generalizationHull_eq]
  intro a b hab ha
  obtain ⟨y, hys, hay⟩ := ha
  obtain ⟨c, hc_closed, hyc⟩ := exists_isClosed_specializes y
  have hcs : c ∈ s := hs hyc hys
  have hac : a ⤳ c := hay.trans hyc
  obtain ⟨c', hc'_closed, hbc'⟩ := exists_isClosed_specializes b
  have hac' : a ⤳ c' := hab.trans hbc'
  obtain rfl := WLocalSpace.eq_of_specializes hc_closed hc'_closed hac hac'
  exact ⟨c, hcs, hbc'⟩

lemma Topology.IsClosedEmbedding.wLocalSpace {f : X → Y} (hf : IsClosedEmbedding f)
    [WLocalSpace Y] : WLocalSpace X where
  toSpectralSpace := hf.spectralSpace
  eq_of_specializes {x c c'} hc hc' hxc hxc' := by
    have hfc : IsClosed ({f c} : Set Y) := by
      rw [← Set.image_singleton]; exact hf.isClosedMap _ hc
    have hfc' : IsClosed ({f c'} : Set Y) := by
      rw [← Set.image_singleton]; exact hf.isClosedMap _ hc'
    exact hf.injective (WLocalSpace.eq_of_specializes hfc hfc'
      (hxc.map hf.continuous) (hxc'.map hf.continuous))
  isClosed_closedPoints := by
    have : closedPoints X = f ⁻¹' closedPoints Y := by
      ext x
      simp only [Set.mem_preimage, mem_closedPoints_iff]
      constructor
      · intro hx
        rw [← Set.image_singleton]
        exact hf.isClosedMap _ hx
      · intro hfx
        rwa [hf.isClosed_iff_image_isClosed, Set.image_singleton]
    rw [this]
    exact WLocalSpace.isClosed_closedPoints.preimage hf.continuous

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
