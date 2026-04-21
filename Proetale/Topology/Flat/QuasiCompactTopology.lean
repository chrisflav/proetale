/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Preserves
import Proetale.Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Proetale.Mathlib.AlgebraicGeometry.Extensive
import Proetale.Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Sites.CoproductSheafCondition
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Proetale.Mathlib.CategoryTheory.Sites.IsSheafFor
import Proetale.Topology.Flat.QuasiCompactCover
import Mathlib.CategoryTheory.Extensive

/-!
# The quasi-compact topology of a scheme

The `qc`-pretopology of a scheme wrt. to a morphism property `P` is the pretopology
given by quasi compact covers satisfying `P`.

We show that a presheaf is a sheaf in this topology if and only if it is a sheaf
in the Zariski topology and a sheaf on single object `P`-coverings of affine schemes.
-/

universe w' w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type*} [Category C] {X : C}

lemma isSheafFor_singleton_iff_of_iso
    {F : Cᵒᵖ ⥤ Type*} {S X Y : C} (f : X ⟶ S) (g : Y ⟶ S)
    (e : X ≅ Y) (he : e.hom ≫ g = f) :
    Presieve.IsSheafFor F (.singleton f) ↔ Presieve.IsSheafFor F (.singleton g) := by
  subst he
  rw [← Presieve.ofArrows_pUnit.{_, _, 0}, ← Presieve.ofArrows_pUnit,
    Presieve.isSheafFor_ofArrows_comp_iff]

@[gcongr]
lemma Precoverage.toPretopology_mono {C : Type*} [Category C] [Limits.HasPullbacks C]
    {J K : Precoverage C} [J.HasIsos] [J.IsStableUnderBaseChange] [J.IsStableUnderComposition]
    [K.HasIsos] [K.IsStableUnderBaseChange] [K.IsStableUnderComposition]
    (h : J ≤ K) : J.toPretopology ≤ K.toPretopology :=
  h

end CategoryTheory

namespace AlgebraicGeometry

open Scheme

variable {P : MorphismProperty Scheme.{u}}

end AlgebraicGeometry
