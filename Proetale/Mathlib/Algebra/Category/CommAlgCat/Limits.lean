import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Proetale.Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct

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

instance preservesFilteredColimitsOfSize_forget (R : Type u) [CommRing R] :
    PreservesFilteredColimitsOfSize (forget (CommAlgCat.{u} R)) :=
  sorry

instance preservesLimitsOfSize_forget (R : Type u) [CommRing R] :
    PreservesLimitsOfSize.{u, u} (forget (CommAlgCat.{u} R)) :=
  sorry

instance : ReflectsFilteredColimitsOfSize.{u, u} (forget (CommAlgCat.{u} R)) where
  reflects_filtered_colimits _ _ _ := reflectsColimitsOfShape_of_reflectsIsomorphisms

instance : IsIPC.{u} (CommAlgCat.{u} R) :=
  .of_preservesFilteredColimitsOfSize (forget (CommAlgCat.{u} R))

section Pi

variable {ι : Type u} (S : ι → CommAlgCat.{u} R)

/-- The fan given by the type theoretic product. -/
@[simps! pt]
def piFan : Fan S :=
  Fan.mk (.of R (∀ i, S i)) fun i ↦ ofHom <| Pi.evalAlgHom _ _ i

/-- The categorical product of `R`-algebras is the type theoretic product. -/
def isLimitPiFan : IsLimit (piFan S) :=
  sorry

end Pi

end CommAlgCat

instance AlgCat.preservesFilteredColimitsOfSize_forget_moduleCat (R : Type u) [CommRing R] :
    PreservesFilteredColimitsOfSize (forget₂ (AlgCat R) (ModuleCat R)) :=
  sorry
