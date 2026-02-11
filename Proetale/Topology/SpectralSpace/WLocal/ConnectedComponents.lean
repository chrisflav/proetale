/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten, Yiming Fu
-/
import Proetale.Mathlib.Order.BooleanAlgebra.Set
import Proetale.Topology.SpectralSpace.ConnectedComponent
import Proetale.Topology.SpectralSpace.WLocal.ClosedPoints

/-!
# Connected components of w-local spaces

This file establishes the relationship between closed points and connected components
in w-local spaces.

## Main results

* `WLocalSpace.isHomeomorph_connectedComponents_closedPoints`: The composition
  `closedPoints X → X → ConnectedComponents X` is a homeomorphism for w-local spaces.
* `WLocalSpace.closedPointsHomeomorph`: The closed points of a w-local space are
  homeomorphic to the connected components.

-/

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
    have hU_clopen : IsClopen U :=
      ⟨hU_closed, hUV_compl.eq_compl.symm ▸ hV_closed.isOpen_compl⟩
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
noncomputable def
    WLocalSpace.closedPointsHomeomorph {X : Type*} [TopologicalSpace X] [WLocalSpace X] :
    closedPoints X ≃ₜ ConnectedComponents X :=
  (WLocalSpace.isHomeomorph_connectedComponents_closedPoints X).homeomorph
