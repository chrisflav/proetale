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

omit [CompactSpace X] [QuasiSeparatedSpace X] in
lemma foo (S : Set X) (B : Set X)
  (hB : IsOpen B) (h2 : IsCompact (S ∩ B))
  : ∃ U ⊆ B, IsOpen U ∧ IsCompact U ∧ S ∩ U = S ∩ B := by
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
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heq] 
    intro i hi
    simp at hi
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    grind
  · exact isOpen_biUnion (fun i hi ↦ i.1.2)
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
  set S : Set X := ⋂ (U : {U : Set X // IsClopen U ∧ x ∈ U}), U
  have hx : x ∈ S := by
    simp [S]
  apply subset_antisymm
  · apply IsConnected.subset_connectedComponent _ hx
    by_contra h
    simp only [IsConnected, not_and] at h
    have := h ⟨x, by simp [S]⟩
    simp only [IsPreconnected, not_forall] at this

    have : ∃ (U V : Set X), IsOpen U ∧ IsOpen V ∧ IsCompact U ∧
        IsCompact V ∧ (U ∩ V) ∩ S = ∅ ∧ S ⊆ U ∪ V ∧ (U ∩ S).Nonempty ∧ (V ∩ S).Nonempty := by
      obtain ⟨B, C, hB, hC, hBC, hBn, hCn, h⟩ := this
      push_neg at h
      have hS : IsClosed S := by
        refine isClosed_iInter ?_
        intro U
        exact U.2.1.1

      obtain ⟨U, hUB, hU, hUc, hUSB⟩ := foo S B hB <| by
        apply IsClosed.isCompact
        convert IsClosed.sdiff hS hC using 1
        tauto_set

      obtain ⟨V, hVB, hV, hVc, hVSC⟩ := foo S C hC <| by
        apply IsClosed.isCompact
        convert IsClosed.sdiff hS hB using 1
        tauto_set

      use U, V, hU, hV, hUc, hVc
      refine ⟨?_, ?_, ?_⟩
      · grind
      · trans (S ∩ U) ∪ (S ∩ V)
        · rw [hUSB, hVSC, ← Set.inter_union_distrib_left]
          simp [hBC]
        · rw [← Set.inter_union_distrib_left]
          exact Set.inter_subset_right
      · rw [U.inter_comm, V.inter_comm, hUSB, hVSC]
        exact ⟨hBn, hCn⟩
    obtain ⟨U, V, hU, hV, hUc, hVc, hUVS, hSUV, hUSn, hVSn⟩ := this

    have : Nonempty {U // IsClopen U ∧ x ∈ U} := ⟨⟨⊤, by simp [isClopen_univ]⟩⟩

    have : ∃ W : Set X, x ∈ W ∧ IsClopen W ∧ U ∩ V ∩ W = ∅ := by
      obtain ⟨W, hW⟩ := IsCompact.elim_directed_family_closed
        (IsCompact.inter_of_isOpen hUc hVc hU hV) _ (·.2.1.1) hUVS
        fun i j ↦ ⟨⟨i.1 ∩ j.1, i.2.1.inter j.2.1, i.2.2, j.2.2⟩, by simp⟩
      use W, W.2.2, W.2.1

    obtain ⟨W, hxW, hW, hUVW⟩ := this

    have : ∃ W' : Set X, x ∈ W' ∧ IsClopen W' ∧ W' ⊆ U ∪ V := by
      have : (U ∪ V)ᶜ ∩ S = ∅ := by
        rwa [← Set.diff_eq_compl_inter, Set.diff_eq_empty]

      obtain ⟨W', hW'⟩ := IsCompact.elim_directed_family_closed
        ((hU.union hV).isClosed_compl.isCompact) _ (·.2.1.1) this
        fun i j ↦ ⟨⟨i.1 ∩ j.1, i.2.1.inter j.2.1, i.2.2, j.2.2⟩, by simp⟩
      use W', W'.2.2, W'.2.1

      rwa [← Set.diff_eq_empty, Set.diff_eq_compl_inter]

    obtain ⟨W', hxW', hW', hW'UV⟩ := this

    set WW := W ∩ W'

    have hUWW : IsClopen (U ∩ WW) := by
      refine ⟨?_, hU.inter (hW.2.inter hW'.2)⟩
      convert IsClosed.sdiff (hW.1.inter hW'.1) hV using 1
      unfold WW
      clear * - hUVW hW'UV
      tauto_set

    have hVWW : IsClopen (V ∩ WW) := by
      refine ⟨?_, hV.inter (hW.2.inter hW'.2)⟩
      convert IsClosed.sdiff (hW.1.inter hW'.1) hU using 1
      unfold WW
      clear * - hUVW hW'UV
      tauto_set

    obtain (hxU | hxV) := hSUV hx

    · apply hVSn.elim
      intro y hy
      have hS : S ⊆ U ∩ WW := by
        fapply Set.iInter_subset_of_subset
        exact ⟨_, hUWW, ⟨hxU, ⟨hxW, hxW'⟩⟩⟩
        rfl
      have : y ∈ U ∩ V ∩ S := by
        grind?
      simp [hUVS] at this
    · apply hUSn.elim
      intro y hy
      have hS : S ⊆ V ∩ WW := by
        fapply Set.iInter_subset_of_subset
        exact ⟨_, hVWW, ⟨hxV, ⟨hxW, hxW'⟩⟩⟩
        rfl
      have : y ∈ U ∩ V ∩ S := by
        grind
      simp [hUVS] at this
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
