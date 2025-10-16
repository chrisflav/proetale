/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
import Mathlib.Topology.Spectral.Hom
import Mathlib.Topology.JacobsonSpace
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems

universe u

-- To be modified
class WLocalSpace (X : Type u) [TopologicalSpace X] : Prop where
  open_cover_splits {I : Type u} {U : I → Set X} (ho : ∀ (i : I), IsOpen (U i)) (hU : ⋃ (i : I), U i = Set.univ) : ∃ s : C(X, (i : I) × U i), ∀ (i : I) (u : U i), s u = ⟨i, u⟩
  isClosed_closedPoints : IsClosed (closedPoints X)

structure IsWLocalMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) : Prop extends IsSpectralMap f where
  range_closedPoints' : f '' (closedPoints X) ⊆ closedPoints Y


def WLocalSpace.closedPointsHomeomorph {X : Type*} [TopologicalSpace X] [WLocalSpace X] : closedPoints X ≃ₜ ConnectedComponents X := sorry
