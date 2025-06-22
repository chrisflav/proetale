import Mathlib.CategoryTheory.Sites.Canonical

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C]

instance GrothendieckTopology.preservesLimitsOfShape_yoneda (J : GrothendieckTopology C)
    [J.Subcanonical] {I : Type*} [Category I] :
    PreservesLimitsOfShape I J.yoneda :=
  have : PreservesLimitsOfShape I (J.yoneda ⋙ sheafToPresheaf J _) :=
    inferInstanceAs <| PreservesLimitsOfShape I CategoryTheory.yoneda
  CategoryTheory.Limits.preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf J _)

end CategoryTheory
