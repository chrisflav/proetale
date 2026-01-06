import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.CategoryTheory.Limits.Preserves.Filtered

universe u

open CategoryTheory Limits

variable {R : Type u} [CommRing R]

instance {J : Type*} [Category J] (M : CommAlgCat R) :
    PreservesColimitsOfShape J (MonoidalCategory.tensorLeft M) :=
  sorry

instance : PreservesColimits (forget₂ (CommAlgCat R) CommRingCat) :=
  sorry

instance (R : Type u) [CommRing R] :
    PreservesFilteredColimitsOfSize (forget₂ (CommAlgCat R) (AlgCat R)) :=
  sorry

instance (R : Type u) [CommRing R] :
    PreservesFilteredColimitsOfSize (forget₂ (AlgCat R) (ModuleCat R)) :=
  sorry
