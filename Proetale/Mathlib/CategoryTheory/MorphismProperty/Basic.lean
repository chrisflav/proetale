import Mathlib.CategoryTheory.MorphismProperty.Basic

open CategoryTheory

@[simp]
lemma CategoryTheory.MorphismProperty.inverseImage_le {C D : Type*} [Category* C]
    [Category* D] (F : C ⥤ D) :
    (⊤ : MorphismProperty D).inverseImage F = ⊤ :=
  rfl
