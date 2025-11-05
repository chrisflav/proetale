/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Topology.Preliminaries.ConnectedComponent
import Mathlib.Topology.Spectral.Basic
import Proetale.Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.Profinite.Basic

/-!
# Connected Component in Spectral Space

Profiniteness is expressed as [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]

-/

universe u

variable {X : Type u} [TopologicalSpace X]

section

variable [CompactSpace X] [QuasiSeparatedSpace X] [PrespectralSpace X]

open TopologicalSpace
lemma foo (S : Set X) (h : IsClosed S) (B : Set X)
  (hB : IsOpen B) (h2 : IsCompact (S ∩ B))
  : ∃ U : Set X, IsOpen U ∧ IsCompact U ∧ S ∩ U = S ∩ B := by
  have := Opens.isBasis_iff_cover.mp (PrespectralSpace.isBasis_opens X)
  have := this ⟨B, hB⟩
  obtain ⟨Us, hUs, hUsC⟩ := this

  have heq := congr($(hUsC).carrier)
  simp at heq
  have := h2.elim_finite_subcover (U := fun i : Us ↦ i.1) (fun i ↦ i.1.2) (by
    rw [heq]
    simp)
  obtain ⟨t, ht⟩ := this
  use ⋃ i ∈ t, i
  constructor
  · exact isOpen_biUnion (fun i hi ↦ i.1.2)
  · constructor
    · apply t.finite_toSet.isCompact_biUnion
      intro i hi
      exact hUs i.2
    · refine subset_antisymm ?_ (by simpa using ht)
      rw [heq]
      gcongr
      intro i hi
      simp at hi
      simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
      grind

@[simp, stacks 005F]
theorem sInter_isClopen_and_mem_eq_connectedComponent {x : X} :
    ⋂ (U : {U : Set X // IsClopen U ∧ x ∈ U}), U = connectedComponent x := by
  apply subset_antisymm
  · apply IsConnected.subset_connectedComponent
    · by_contra h

      simp only [IsConnected, not_and] at h
      have := h ⟨x, by simp⟩
      simp only [IsPreconnected, not_forall] at this
      obtain ⟨B', C', hB', hC', hBC', hBn', hCn', h⟩ := this
      push_neg at h

      sorry
    · simp
  · exact connectedComponent_subset_iInter_isClopen

@[stacks 04PL]
theorem isClosed_and_iUnion_connectedComponent_iff {T : Set X} :
    (IsClosed T ∧ ∃ I : Set X, ⋃ (x : I), connectedComponent x = T) ↔
    ∃ J : Set ({U : Set X // IsClopen U}), ⋂ (U : J), U = T := by
  sorry
  -- uses `ConnectedComponents.injective_lift`

@[stacks 0906]
instance compactSpace_connectedComponent : CompactSpace (ConnectedComponents X) := sorry

@[stacks 0906]
instance t2Space_connectedComponent : T2Space (ConnectedComponents X) := sorry

end

section Spectral

variable [SpectralSpace X]

#check ConnectedComponents.lift
open CategoryTheory TopCat ConnectedComponents

-- TBModified
@[stacks 096C "first part"]
theorem spectralSpace_of_isPullback_mk (Y T : Type u) [TopologicalSpace Y]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    (f : C(Y, X)) (g : C(Y, T)) (i : C(T, ConnectedComponents X))
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    SpectralSpace Y := sorry

-- open Profinite

-- @[stacks 096C "first part"]
-- theorem spectralSpace_of_isPullback_mk' (X Y : TopCat) (T : Profinite) (f : Y ⟶ X) (g : Y ⟶ toTopCat.obj T) (i : toTopCat.obj T ⟶ of (ConnectedComponents X)) (pb : IsPullback g f i (ofHom ⟨mk, continuous_coe⟩ : X ⟶ of (ConnectedComponents X))) : SpectralSpace Y := sorry

end Spectral
