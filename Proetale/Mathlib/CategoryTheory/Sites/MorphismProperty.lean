import Mathlib.CategoryTheory.Sites.MorphismProperty

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category C] {P : MorphismProperty C}

@[simp]
lemma singleton_mem_precoverage_iff {X Y : C} {f : X ⟶ Y} :
    Presieve.singleton f ∈ P.precoverage Y ↔ P f := by
  simp [← Presieve.ofArrows_pUnit.{_, _, 0}]

instance : P.precoverage.IsStableUnderSup where
  sup_mem_coverings hR hS Y f hf := by
    obtain (h|h) := hf
    exact hR h
    exact hS h

end CategoryTheory.MorphismProperty
