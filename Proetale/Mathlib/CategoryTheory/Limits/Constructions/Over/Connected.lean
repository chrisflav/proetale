import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

namespace CategoryTheory.CostructuredArrow

open Limits

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (X : D)

-- this is in #30074
instance (J : Type*) [Category J] [IsConnected J] :
    PreservesLimitsOfShape J (CostructuredArrow.proj F X) :=
  sorry

-- this is in #30074
instance (J : Type*) [Category J] [IsConnected J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (CostructuredArrow F X) :=
  sorry

end CategoryTheory.CostructuredArrow
