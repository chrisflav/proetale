import Mathlib.CategoryTheory.Sites.Sieves

namespace CategoryTheory

variable {C : Type*} [Category C]

@[simp]
lemma Sieve.generate_bot {X : C} : Sieve.generate (⊥ : Presieve X) = ⊥ := by
  rw [eq_bot_iff]
  rintro Y f ⟨Z, g, u, hg, rfl⟩
  exact hg

end CategoryTheory
