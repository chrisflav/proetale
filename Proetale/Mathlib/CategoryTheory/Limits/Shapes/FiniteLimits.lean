import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

namespace CategoryTheory.Limits

variable {C : Type*} [Category C]

instance (J : Type*) [Finite J] [HasFiniteWidePullbacks C] :
    HasLimitsOfShape (WidePullbackShape J) C := by
  cases nonempty_fintype J
  apply hasLimitsOfShape_of_equivalence
    (WidePullbackShape.equivalenceOfEquiv _ (Fintype.equivFin J).symm)

end CategoryTheory.Limits
