/-
Copyright (c) 2025 Jiang Jiedong, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiang Jiedong, Christian Merten
-/
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Closures in categorical limits of topological spaces.

-/

open CategoryTheory Limits

theorem TopCat.closure_eq_iInter_preimage_closure_image {I : Type*} [Category I]
    {F : Functor I TopCat} {C : Cone F} (hC : IsLimit C) (s : Set C.pt) :
    closure s = ⋂ (i : I), (C.π.app i)⁻¹' (closure ((C.π.app i)'' s)) :=
  sorry

theorem image_closure_image_subset_closure_image {I : Type*} [Category I]
    {F : Functor I TopCat} (C : Cone F) (s : Set C.pt) {i j : I} (f : i ⟶ j) :
    (F.map f) '' (closure ((C.π.app i) '' s)) ⊆ closure ((C.π.app j) '' s) :=
  sorry
  -- image_closure_subset_closure_image
