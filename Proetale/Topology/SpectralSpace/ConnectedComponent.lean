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

@[simp, stacks 005F]
theorem sInter_isClopen_and_mem_eq_connectedComponent {x : X} :
    ⋂ (U : {U : Set X // IsClopen U ∧ x ∈ U}), U = connectedComponent x := by
  apply subset_antisymm
  · sorry
  · exact connectedComponent_subset_iInter_isClopen

@[stacks 04PL]
theorem isClosed_and_iUnion_connectedComponent_iff {T : Set X} :
    (IsClosed T ∧ ∃ I : Set X, ⋃ (x : I), connectedComponent x = T) ↔
    ∃ J : Set ({U : Set X // IsClopen U}), ⋂ (U : J), U = T := by
  sorry
  -- uses `ConnectedComponents.injective_lift`

@[stacks 0906]
instance compactSpace_connectedComponent {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [QuasiSeparatedSpace X] [PrespectralSpace X] : CompactSpace (ConnectedComponents X) :=
  sorry

@[stacks 0906]
instance t2Space_connectedComponent {X : Type u} [TopologicalSpace X]  [CompactSpace X]
    [QuasiSeparatedSpace X] [PrespectralSpace X] : T2Space (ConnectedComponents X) :=
  sorry

end

section Spectral

variable [SpectralSpace X]

#check ConnectedComponents.lift
open CategoryTheory TopCat ConnectedComponents

theorem spectralSpace_of_isPullback_mk (Y T : Type u) [TopologicalSpace Y]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    (f : C(Y, X)) (g : C(Y, T)) (i : C(T, ConnectedComponents X))
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    SpectralSpace Y := sorry

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
