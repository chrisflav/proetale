/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Topology.Preliminaries.ConnectedComponent
import Mathlib.Topology.Spectral.Prespectral

/-!
# Connected Component in Spectral Space

-/

@[simp, stacks 005F]
theorem sInter_isClopen_and_mem_eq_connectedComponent {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [QuasiSeparatedSpace X] [PrespectralSpace X] {x : X} :
    ⋂ (U : {U : Set X // IsClopen U ∧ x ∈ U}), U = connectedComponent x := by
  apply subset_antisymm
  · sorry
  · exact connectedComponent_subset_iInter_isClopen

@[stacks 04PL]
theorem isClosed_and_iUnion_connectedComponent_iff {X : Type*} [TopologicalSpace X] [CompactSpace X] [QuasiSeparatedSpace X] [PrespectralSpace X] {T : Set X} :
    (IsClosed T ∧ ∃ I : Set X, ⋃ (x : I), connectedComponent x = T) ↔
    ∃ J : Set ({U : Set X // IsClopen U}), ⋂ (U : J), U = T := by
  sorry
  -- uses `ConnectedComponents.injective_lift`
