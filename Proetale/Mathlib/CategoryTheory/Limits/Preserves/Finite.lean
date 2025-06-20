import Mathlib.CategoryTheory.Limits.Preserves.Finite

universe v

namespace CategoryTheory

variable {C : Type*} [Category C]

lemma Limits.preservesFiniteProducts_of_preservesLimitsOfShape {D : Type*} [Category D] (F : C ⥤ D)
    (H : ∀ (ι : Type v) [Finite ι], PreservesLimitsOfShape (Discrete ι) F) :
    PreservesFiniteProducts F := by
  constructor
  intro n
  exact preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) F

end CategoryTheory
