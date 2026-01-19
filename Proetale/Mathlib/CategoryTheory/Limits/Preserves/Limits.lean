import Mathlib.CategoryTheory.Limits.Preserves.Limits

namespace CategoryTheory

open Limits

lemma preservesColimit_iff_isIso_post {C : Type*} [Category* C] {D : Type*} [Category* D]
    (G : C ⥤ D) {J : Type*} [Category* J] (F : J ⥤ C) [HasColimit F]
    [HasColimit (F ⋙ G)] :
    PreservesColimit F G ↔ IsIso (colimit.post F G) := by
  refine ⟨fun h ↦ inferInstance, fun h ↦ preservesColimit_of_isIso_post G F⟩

end CategoryTheory
