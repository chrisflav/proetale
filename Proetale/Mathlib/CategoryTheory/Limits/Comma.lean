import Mathlib.CategoryTheory.Limits.Comma

namespace CategoryTheory

open Limits

variable {A B T : Type*} [Category A] [Category B] [Category T]
  (L : A ⥤ T) (R : B ⥤ T)
variable {J : Type*} [Category J]

namespace Comma

instance preservesLimitsOfShape_fst [HasLimitsOfShape J A] [HasLimitsOfShape J B]
    [PreservesLimitsOfShape J R] : PreservesLimitsOfShape J (Comma.fst L R) where
  preservesLimit :=
    preservesLimit_of_preserves_limit_cone
      (coneOfPreservesIsLimit _ (limit.isLimit _) (limit.isLimit _))
      (limit.isLimit _)

instance preservesLimitsOfShape_snd [HasLimitsOfShape J A] [HasLimitsOfShape J B]
    [PreservesLimitsOfShape J R] : PreservesLimitsOfShape J (Comma.snd L R) where
  preservesLimit :=
    preservesLimit_of_preserves_limit_cone
      (coneOfPreservesIsLimit _ (limit.isLimit _) (limit.isLimit _))
      (limit.isLimit _)

end Comma

end CategoryTheory
