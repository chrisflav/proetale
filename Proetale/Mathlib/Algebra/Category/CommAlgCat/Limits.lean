import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.CategoryTheory.Limits.Preserves.Filtered

universe u

open CategoryTheory Limits

namespace CommAlgCat

variable {R : Type u} [CommRing R]

instance preservesColimitsOfShape_tensorLeft
    {J : Type*} [Category J] (M : CommAlgCat R) :
    PreservesColimitsOfShape J (MonoidalCategory.tensorLeft M) :=
  sorry

instance preservesColimitsOfSize_forget_commRingCat :
    PreservesColimits (forget₂ (CommAlgCat R) CommRingCat) :=
  sorry

instance preservesFilteredColimitsOfSize_forget_algCat (R : Type u) [CommRing R] :
    PreservesFilteredColimitsOfSize (forget₂ (CommAlgCat R) (AlgCat R)) :=
  sorry

end CommAlgCat

instance AlgCat.preservesFilteredColimitsOfSize_forget_moduleCat (R : Type u) [CommRing R] :
    PreservesFilteredColimitsOfSize (forget₂ (AlgCat R) (ModuleCat R)) :=
  sorry
