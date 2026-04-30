import Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty

namespace CategoryTheory.MorphismProperty

@[simp]
lemma ofObjectProperty_top_right_iff {C : Type*} [Category* C] {X Y : C} {f : X ⟶ Y}
    {P : ObjectProperty C} :
    ofObjectProperty P ⊤ f ↔ P X :=
  ⟨fun h ↦ h.left, fun h ↦ ⟨h, trivial⟩⟩

@[simp]
lemma ofObjectProperty_top_left_iff {C : Type*} [Category* C] {X Y : C} {f : X ⟶ Y}
    {P : ObjectProperty C} :
    ofObjectProperty ⊤ P f ↔ P Y :=
  ⟨fun h ↦ h.right, fun h ↦ ⟨trivial, h⟩⟩

end CategoryTheory.MorphismProperty
