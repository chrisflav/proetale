import Mathlib.CategoryTheory.Sites.Precoverage

namespace CategoryTheory

variable {C : Type*} [Category C] {K : Precoverage C}

lemma Precoverage.mem_coverings_singleton_of_isPullback [K.IsStableUnderBaseChange]
    {X Y Z P : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback fst snd f g) (hg : Presieve.singleton g ∈ K Z) :
    Presieve.singleton fst ∈ K X := by
  rw [← Presieve.ofArrows_pUnit] at hg ⊢
  apply K.mem_coverings_of_isPullback _ hg
  intro _
  apply h

end CategoryTheory
