/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.Topology.Bases
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Topology.Category.TopCat.Limits.Cofiltered

/-!
# Closures in categorical limits of topological spaces.

-/

open CategoryTheory Limits

universe u v w

theorem TopCat.closure_eq_iInter_preimage_closure_image {I : Type v} [Category.{w} I]
    [IsCofiltered I] {F : Functor I TopCat.{max v u}} {C : Cone F} (hC : IsLimit C) (s : Set C.pt) :
    closure s = ⋂ (i : I), (C.π.app i)⁻¹' (closure ((C.π.app i)'' s)) := by
  refine Set.Subset.antisymm (Set.subset_iInter_iff.2 fun i ↦ ?_) fun x hx ↦ ?_
  · simpa using closure_subset_preimage_closure_image (f := C.π.app i) (s := s)
      (C.π.app i).hom.continuous
  have hB : TopologicalSpace.IsTopologicalBasis
      {U : Set C.pt | ∃ (j : I) (V : Set (F.obj j)), IsOpen V ∧ U = (C.π.app j) ⁻¹' V} := by
    simpa using TopCat.isTopologicalBasis_cofiltered_limit.{u, v, w} (C := C) (hC := hC)
      (T := fun j ↦ {V : Set (F.obj j) | IsOpen V})
      (hT := fun _ ↦ TopologicalSpace.isTopologicalBasis_opens)
      (univ := fun _ ↦ by simp)
      (inter := fun _ _ _ h1 h2 ↦ by simpa using h1.inter h2)
      (compat := fun _ _ f _ hV ↦ by simpa using hV.preimage (F.map f).hom.continuous)
  refine (hB.mem_closure_iff (s := s) (a := x)).2 ?_
  rintro _ ⟨j, V, hVopen, rfl⟩ hxo
  have hxj : (C.π.app j) x ∈ closure ((C.π.app j) '' s) := by
    simpa using Set.mem_iInter.mp hx j
  obtain ⟨z, hzV, y, hyS, rfl⟩ := mem_closure_iff.1 hxj V hVopen hxo
  exact ⟨y, hzV, hyS⟩

theorem image_closure_image_subset_closure_image {I : Type*} [Category I]
    {F : Functor I TopCat} (C : Cone F) (s : Set C.pt) {i j : I} (f : i ⟶ j) :
    (F.map f) '' (closure ((C.π.app i) '' s)) ⊆ closure ((C.π.app j) '' s) := by
  have himage : (F.map f) '' ((C.π.app i) '' s) = (C.π.app j) '' s := by
    rw [Set.image_image]
    refine Set.image_congr fun x _ ↦ ?_
    exact congrArg (fun g : C.pt ⟶ F.obj j ↦ ConcreteCategory.hom g x) (C.w f)
  simpa [himage] using image_closure_subset_closure_image (f := F.map f)
    (s := (C.π.app i) '' s) (F.map f).hom.continuous
