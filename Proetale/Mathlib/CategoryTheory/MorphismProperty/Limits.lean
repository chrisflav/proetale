import Mathlib.CategoryTheory.MorphismProperty.Limits

namespace CategoryTheory

open Limits MorphismProperty

instance {C : Type*} [Category C] [HasPullbacks C] (P : MorphismProperty C) [P.ContainsIdentities]
    [P.RespectsIso] :
    (diagonal P).ContainsIdentities where
  id_mem X := by
    change P _
    rw [← Category.id_comp (pullback.diagonal _), P.cancel_right_of_respectsIso]
    exact P.id_mem X


end CategoryTheory
