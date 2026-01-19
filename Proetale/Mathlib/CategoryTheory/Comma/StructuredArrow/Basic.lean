import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

namespace CategoryTheory

@[simps! obj_left obj_hom map_left]
def CostructuredArrow.lift {J C D : Type*} [Category* J] [Category* C] [Category* D]
    (F : J ⥤ C)
    {L : C ⥤ D} {X : D} (s : F ⋙ L ⟶ (Functor.const _).obj X) :
    J ⥤ CostructuredArrow L X where
  obj j := .mk (s.app j)
  map {i j} f := CostructuredArrow.homMk (F.map f) (by simp [← Functor.comp_map])

@[simp]
lemma CostructuredArrow.lift_forget {J C D : Type*} [Category* J] [Category* C] [Category* D]
    (F : J ⥤ C) {L : C ⥤ D} {X : D} (s : F ⋙ L ⟶ (Functor.const _).obj X) :
    lift F s ⋙ CategoryTheory.CostructuredArrow.proj _ _ = F :=
  rfl

end CategoryTheory
