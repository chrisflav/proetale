import Mathlib.CategoryTheory.Sites.Sieves

namespace CategoryTheory

variable {C : Type*} [Category C]

lemma Presieve.functorPullback_monotone {D : Type*} [Category D] (F : C ⥤ D) (X : C) :
    Monotone (functorPullback F (X := X)) :=
  fun _ _ hle _ _ hf ↦ hle _ hf

lemma Presieve.uncurry_sup {X : C} (R S : Presieve X) :
    (R ⊔ S).uncurry = R.uncurry ∪ S.uncurry := rfl

lemma Presieve.uncurry_inf {X : C} (R S : Presieve X) :
    (R ⊓ S).uncurry = R.uncurry ∩ S.uncurry := rfl

end CategoryTheory
