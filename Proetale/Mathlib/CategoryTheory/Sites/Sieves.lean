import Mathlib.CategoryTheory.Sites.Sieves

namespace CategoryTheory

variable {C : Type*} [Category C]

@[simp]
lemma Sieve.generate_bot {X : C} : Sieve.generate (⊥ : Presieve X) = ⊥ := by
  rw [eq_bot_iff]
  rintro Y f ⟨Z, g, u, hg, rfl⟩
  exact hg

lemma Sieve.generate_mono {X : C} {R₁ R₂ : Presieve X} (h : R₁ ≤ R₂) :
    Sieve.generate R₁ ≤ Sieve.generate R₂ :=
  Sieve.giGenerate.gc.monotone_l h

lemma Presieve.functorPullback_monotone {D : Type*} [Category D] (F : C ⥤ D) (X : C) :
    Monotone (functorPullback F (X := X)) :=
  fun _ _ hle _ _ hf ↦ hle _ hf

lemma Presieve.uncurry_sup {X : C} (R S : Presieve X) :
    (R ⊔ S).uncurry = R.uncurry ∪ S.uncurry := rfl

lemma Presieve.uncurry_inf {X : C} (R S : Presieve X) :
    (R ⊓ S).uncurry = R.uncurry ∩ S.uncurry := rfl

end CategoryTheory
