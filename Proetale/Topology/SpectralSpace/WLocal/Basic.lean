/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten, Yiming Fu
-/
import Proetale.Mathlib.Order.BooleanAlgebra.Set
import Proetale.Mathlib.Topology.JacobsonSpace
import Proetale.Mathlib.Topology.Separation.Basic
import Proetale.Topology.SpectralSpace.ConnectedComponent
import Proetale.Topology.SpectralSpace.Constructible
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.Spectral.Basic
/-!
#### w-local spaces

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

section closedPoints

variable {X : Type*} [TopologicalSpace X]

namespace WLocalSpace

instance spectralSpace_closedPoints [WLocalSpace X] : SpectralSpace (closedPoints X) :=
  SpectralSpace.of_isClosed X

instance t2Space_closedPoints [WLocalSpace X] :
    T2Space (closedPoints X) :=
  SpectralSpace.t2Space_of_isClosed_singleton  closedPoints.isClosed_singleton

instance CompactSpace_closedPoints [WLocalSpace X] :
    CompactSpace (closedPoints X) :=
  (IsClosed.isClosedEmbedding_subtypeVal inferInstance).compactSpace

instance totallyDisconnected_closedPoints [WLocalSpace X] :
    TotallyDisconnectedSpace (closedPoints X) :=
  SpectralSpace.totallyDisconnectedSpace_of_isClosed_singleton closedPoints.isClosed_singleton

end WLocalSpace

end closedPoints

/-- A w-local map is a spectral map that maps closed points to closed points. -/
@[mk_iff]
structure IsWLocalMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) : Prop
    extends IsSpectralMap f where
  preimage_closedPoints : f ⁻¹' (closedPoints Y) ⊆ closedPoints X

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

lemma IsWLocalMap.comp {Z : Type*} [TopologicalSpace Z] {f : X → Y} {g : Y → Z}
    (hf : IsWLocalMap f) (hg : IsWLocalMap g) :
    IsWLocalMap (g ∘ f) where
  toIsSpectralMap := IsSpectralMap.comp hg.toIsSpectralMap hf.toIsSpectralMap
  preimage_closedPoints := fun _ hx => hf.preimage_closedPoints <|
    hg.preimage_closedPoints <| Set.mem_preimage.2 <| hx

theorem Topology.IsInducing.isClosed_singleton_of_stableUnderSpecialization_range
  {f : X → Y} (hf : IsInducing f)
  (h : StableUnderSpecialization (Set.range f)) {x : X}
  (hx : IsClosed {x}) : IsClosed {f x} := by
  rw [← closure_eq_iff_isClosed, hf.closure_eq_preimage_closure_image] at hx
  rw [← Set.image_singleton, ← hx, Set.image_preimage_eq_inter_range]
  have : closure {f x} ∩ Set.range f = closure {f x} := by
    rw [Set.inter_eq_left]
    intro y hy
    rw [← specializes_iff_mem_closure] at hy
    exact h hy (Set.mem_range_self x)
  simp only [Set.image_singleton, this, isClosed_closure]

lemma Topology.IsEmbedding.wLocalSpace_of_stableUnderSpecialization_range {f : X → Y}
    (hf : IsEmbedding f) (h : StableUnderSpecialization (Set.range f))
    [SpectralSpace X] [WLocalSpace Y] : WLocalSpace X where
  eq_of_specializes {x c c'} hc hc' hxc hxc' := hf.2 <|
    WLocalSpace.eq_of_specializes
      (hf.1.isClosed_singleton_of_stableUnderSpecialization_range h hc)
      (hf.1.isClosed_singleton_of_stableUnderSpecialization_range h hc')
      (hf.1.specializes_iff.2 hxc)
      (hf.1.specializes_iff.2 hxc')
  isClosed_closedPoints := by
    have : f ⁻¹' closedPoints Y = closedPoints X := Set.Subset.antisymm
      (preimage_closedPoints_subset hf.2 hf.continuous)
      (fun x hx ↦ mem_closedPoints_iff.2 <|
        hf.1.isClosed_singleton_of_stableUnderSpecialization_range h (mem_closedPoints_iff.1 hx))
    simpa [this] using WLocalSpace.isClosed_closedPoints.preimage hf.continuous

lemma StableUnderSpecialization.generalizationHull_of_wLocalSpace [WLocalSpace X] {s : Set X}
    (hs : StableUnderSpecialization s) :
    StableUnderSpecialization (generalizationHull s) := by
  intro x y hxy hx
  rw [mem_generalizationHull_iff] at hx ⊢
  obtain ⟨z, hzs, hxz⟩ := hx
  obtain ⟨c, hc, hzc⟩ := exists_isClosed_specializes z
  obtain ⟨c', hc', hyc'⟩ := exists_isClosed_specializes y
  exact ⟨c, hs hzc hzs, WLocalSpace.eq_of_specializes hc hc'
    (hxz.trans hzc) (hxy.trans hyc') ▸ hyc'⟩

lemma Topology.IsClosedEmbedding.wLocalSpace {f : X → Y} (hf : IsClosedEmbedding f)
    [WLocalSpace Y] : WLocalSpace X :=
  have : SpectralSpace X := hf.spectralSpace
  Topology.IsEmbedding.wLocalSpace_of_stableUnderSpecialization_range
    hf.isEmbedding hf.isClosed_range.stableUnderSpecialization

lemma isClosed_generalizationHull_of_wLocalSpace [WLocalSpace X] {s : Set X} (hs : IsClosed s) :
    IsClosed (generalizationHull s) := by
  obtain ⟨S, hS_sub, heq⟩ := generalizationHull.eq_sInter_of_isCompact X hs.isCompact
  apply IsClosed.of_isClosed_constructibleTopology
  · rw [heq]
    apply @isClosed_sInter _ (constructibleTopology X) S
    intro U hU
    rw [← @isOpen_compl_iff _ _ (constructibleTopology X)]
    have hUc : IsCompact Uᶜᶜ := by simp [(hS_sub hU).2]
    exact hUc.isOpen_constructibleTopology_of_isClosed (isClosed_compl_iff.mpr (hS_sub hU).1)
  · exact hs.stableUnderSpecialization.generalizationHull_of_wLocalSpace

/-- If `X` is w-local, the composition `closedPoints X → X → ConnectedComponents X` is
a homeomorphism. -/
lemma WLocalSpace.isHomeomorph_connectedComponents_closedPoints (X : Type*) [TopologicalSpace X]
    [WLocalSpace X] :
    IsHomeomorph (ConnectedComponents.mk ∘ ((↑) : closedPoints X → X)) := by
  have : CompactSpace (closedPoints X) :=
    (IsClosed.isClosedEmbedding_subtypeVal WLocalSpace.isClosed_closedPoints).compactSpace
  have : T2Space (ConnectedComponents X) := t2Space_connectedComponent
  rw [isHomeomorph_iff_continuous_bijective]
  refine ⟨ConnectedComponents.continuous_coe.comp continuous_subtype_val, ?_, ?_⟩
  · intro ⟨x, hx⟩ ⟨y, hy⟩ heq
    simp only [Function.comp_apply] at heq
    by_contra hxy
    obtain ⟨U₀, hU₀_clopen, hxU₀, hyU₀⟩ := exists_isClopen_of_totally_separated (fun h => hxy h)
    have hce : Topology.IsClosedEmbedding ((↑) : closedPoints X → X) :=
      IsClosed.isClosedEmbedding_subtypeVal WLocalSpace.isClosed_closedPoints
    let U := generalizationHull (Subtype.val '' U₀)
    let V := generalizationHull (Subtype.val '' U₀ᶜ)
    have hU_closed : IsClosed U :=
      isClosed_generalizationHull_of_wLocalSpace (hce.isClosedMap U₀ hU₀_clopen.1)
    have hV_closed : IsClosed V :=
      isClosed_generalizationHull_of_wLocalSpace (hce.isClosedMap U₀ᶜ hU₀_clopen.compl.1)
    have hX_eq : (Set.univ : Set X) = U ∪ V := by
      ext z; simp only [Set.mem_univ, true_iff]
      obtain ⟨c, hc_closed, hzc⟩ := exists_isClosed_specializes z
      have hc_cp : c ∈ closedPoints X := mem_closedPoints_iff.mpr hc_closed
      exact (em (⟨c, hc_cp⟩ ∈ U₀)).imp
        (fun h => mem_generalizationHull_iff.mpr ⟨c, ⟨⟨c, hc_cp⟩, h, rfl⟩, hzc⟩)
        (fun h => mem_generalizationHull_iff.mpr ⟨c, ⟨⟨c, hc_cp⟩, h, rfl⟩, hzc⟩)
    have hUV_disjoint : Disjoint U V := by
      rw [Set.disjoint_iff]
      intro z ⟨hzU, hzV⟩
      rw [mem_generalizationHull_iff] at hzU hzV
      obtain ⟨c, ⟨⟨c', hc'⟩, hc'U₀, rfl⟩, hzc⟩ := hzU
      obtain ⟨d, ⟨⟨d', hd'⟩, hd'V₀, rfl⟩, hzd⟩ := hzV
      exact hd'V₀ (WLocalSpace.eq_of_specializes (mem_closedPoints_iff.mp hc')
        (mem_closedPoints_iff.mp hd') hzc hzd ▸ hc'U₀)
    have hUV_compl : IsCompl U V :=
      ⟨hUV_disjoint, Set.codisjoint_iff.mpr hX_eq.symm⟩
    have hU_clopen : IsClopen U := ⟨hU_closed, hUV_compl.eq_compl.symm ▸ hV_closed.isOpen_compl⟩
    have hxU : x ∈ U :=
      mem_generalizationHull_iff.mpr ⟨x, ⟨⟨x, hx⟩, hxU₀, rfl⟩, specializes_refl x⟩
    have hyV : y ∈ V :=
      mem_generalizationHull_iff.mpr ⟨y, ⟨⟨y, hy⟩, hyU₀, rfl⟩, specializes_refl y⟩
    exact hUV_disjoint.ne_of_mem (hU_clopen.connectedComponent_subset hxU
      (ConnectedComponents.coe_eq_coe'.mp heq.symm)) hyV rfl
  · intro c
    obtain ⟨x, rfl⟩ := c.exists_rep
    obtain ⟨p, hp, hxp⟩ := exists_isClosed_specializes x
    exact ⟨⟨p, mem_closedPoints_iff.mpr hp⟩, ConnectedComponents.coe_eq_coe.mpr
      (connectedComponent_eq_iff_mem.mpr (isConnected_singleton.closure.subset_connectedComponent
        (subset_closure rfl) (specializes_iff_mem_closure.mp hxp)))⟩

/-- The closed points of a w-local space are homeomorphic to the connected components. -/
noncomputable
def WLocalSpace.closedPointsHomeomorph {X : Type*} [TopologicalSpace X] [WLocalSpace X] :
    closedPoints X ≃ₜ ConnectedComponents X :=
  (WLocalSpace.isHomeomorph_connectedComponents_closedPoints X).homeomorph
