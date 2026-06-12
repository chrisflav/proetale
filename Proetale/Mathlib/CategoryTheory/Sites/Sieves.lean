import Mathlib.CategoryTheory.Sites.Sieves

namespace CategoryTheory

variable {C : Type*} [Category C]

lemma Presieve.uncurry_sup {X : C} (R S : Presieve X) :
    (R ⊔ S).uncurry = R.uncurry ∪ S.uncurry := rfl

lemma Presieve.uncurry_inf {X : C} (R S : Presieve X) :
    (R ⊓ S).uncurry = R.uncurry ∩ S.uncurry := rfl

@[simp]
lemma Presieve.map_comp {C D E : Type*} [Category* C] [Category* D]
    [Category* E] (F : C ⥤ D) (G : D ⥤ E) {X : C} (R : Presieve X) :
    R.map (F ⋙ G) = (R.map F).map G := by
  refine le_antisymm ?_ ?_
  · rw [Presieve.map_le_iff_le_functorPullback]
    intro Y f hf
    apply Presieve.map_map
    apply Presieve.map_map
    exact hf
  · rw [Presieve.map_le_iff_le_functorPullback, Presieve.map_le_iff_le_functorPullback]
    intro Y f hf
    apply Presieve.map_map
    exact hf

lemma Presieve.map_functorPullback_of_forall_exists
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {X : C}
    (R : Presieve (F.obj X)) [F.Full]
    (H : ∀ ⦃Y : D⦄ (f : Y ⟶ F.obj X), ∃ (Z : C) (g : Z ⟶ X) (e : F.obj Z = Y),
      F.map g = eqToHom e ≫ f) :
    Presieve.map F (Presieve.functorPullback F R) = R := by
  refine le_antisymm ?_ ?_
  · rw [Presieve.map_le_iff_le_functorPullback]
  · intro Y f hf
    obtain ⟨Z, g, rfl, hg⟩ := H f
    rw [Presieve.map_iff]
    use Z, rfl, g
    simpa [Presieve.functorPullback_mem, hg, and_true]

end CategoryTheory
