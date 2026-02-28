/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Order.Filter.Finite

/-!
# Closures in categorical limits of topological spaces.

-/

open CategoryTheory Limits Filter Topology

theorem TopCat.closure_eq_iInter_preimage_closure_image {I : Type*} [Category I] [IsCofiltered I]
    {F : Functor I TopCat} {C : Cone F} (hC : IsLimit C) (s : Set C.pt) :
    closure s = ⋂ (i : I), (C.π.app i)⁻¹' (closure ((C.π.app i)'' s)) := by
  apply Set.Subset.antisymm
  · -- ⊆ direction: RHS is closed and contains s
    refine closure_minimal ?_ ?_
    · intro x hx
      simp only [Set.mem_iInter, Set.mem_preimage]
      intro i
      exact subset_closure ⟨x, hx, rfl⟩
    · exact isClosed_iInter fun i =>
        (isClosed_closure.preimage (C.π.app i).hom.continuous)
  · -- ⊇ direction: uses the initial topology characterization and IsCofiltered
    -- Blueprint: lemma:closure-limit-intersection. Use initial topology: x ∈ closure s iff π_i(x) ∈ closure(π_i(s)) for all i.
    sorry


theorem image_closure_image_subset_closure_image {I : Type*} [Category I]
    {F : Functor I TopCat} (C : Cone F) (s : Set C.pt) {i j : I} (f : i ⟶ j) :
    (F.map f) '' (closure ((C.π.app i) '' s)) ⊆ closure ((C.π.app j) '' s) := by
  have hnat : C.π.app i ≫ F.map f = C.π.app j := by
    have := C.π.naturality f
    dsimp [Functor.const] at this
    rw [Category.id_comp] at this
    exact this.symm
  have himg : (C.π.app j) '' s = (F.map f) '' ((C.π.app i) '' s) := by
    rw [← hnat, ← Set.image_comp]
    rfl
  rw [himg]
  exact image_closure_subset_closure_image (F.map f).hom.continuous
