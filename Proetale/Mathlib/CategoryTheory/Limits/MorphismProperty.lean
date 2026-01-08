import Mathlib
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Comma

namespace CategoryTheory

lemma Limits.IsColimit.hasColimit {J C : Type*} [Category J] [Category C]
    {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) : HasColimit D := ⟨_, hc⟩

open Limits Comma

variable {T : Type*} [Category T] (P : MorphismProperty T)

namespace MorphismProperty.Comma

variable {A B J : Type*} [Category A] [Category B] [Category J] {L : A ⥤ T} {R : B ⥤ T}
variable (D : J ⥤ P.Comma L R ⊤ ⊤)

end Comma

end MorphismProperty

end CategoryTheory
