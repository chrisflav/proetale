/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits

universe u

open CategoryTheory Limits

instance : ReflectsFilteredColimitsOfSize.{u, u} (forget CommRingCat.{u}) where
  reflects_filtered_colimits _ _ _ := reflectsColimitsOfShape_of_reflectsIsomorphisms

instance : IsIPC.{u} CommRingCat.{u} :=
  .of_preservesFilteredColimitsOfSize (forget CommRingCat.{u})
