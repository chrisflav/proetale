/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.CategoryTheory.Presentable.LocallyPresentable

/-!
# Under categories of `CommRingCat` are finitely accessible

For any `R : CommRingCat.{u}`, the category `Under R` of `R`-algebras is finitely
accessible, meaning every `R`-algebra is a filtered colimit of finitely presented
`R`-algebras (Stacks [00U3](https://stacks.math.columbia.edu/tag/00U3)).
-/

universe u

open CategoryTheory Limits

namespace CommRingCat

/-- For any `R : CommRingCat.{u}`, the category `Under R` is finitely accessible. -/
instance isFinitelyAccessibleCategory_under (R : CommRingCat.{u}) :
    IsFinitelyAccessibleCategory.{u} (Under R) :=
  sorry

end CommRingCat
