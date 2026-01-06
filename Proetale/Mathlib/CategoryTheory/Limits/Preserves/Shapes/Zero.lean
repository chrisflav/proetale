import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

open CategoryTheory Limits

@[simp]
lemma CategoryTheory.Functor.whiskerLeft_zero
    {C D E : Type*} [Category C] [Category D] [Category E] [HasZeroMorphisms E]
    (F : C ⥤ D) (G H : D ⥤ E) :
    Functor.whiskerLeft F (0 : G ⟶ H) = 0 :=
  rfl
