import Mathlib.CategoryTheory.MorphismProperty.Limits

namespace CategoryTheory

instance {C : Type*} [Category C] : (⊤ : MorphismProperty C).IsStableUnderBaseChange where
  of_isPullback _ _ := trivial

end CategoryTheory
