import Mathlib.CategoryTheory.Limits.MorphismProperty

namespace CategoryTheory

open Limits MorphismProperty.Comma

variable {T : Type*} [Category T] (P : MorphismProperty T)

namespace MorphismProperty.Comma

variable {A B J : Type*} [Category A] [Category B] [Category J] {L : A ⥤ T} {R : B ⥤ T}
variable (D : J ⥤ P.Comma L R ⊤ ⊤)

/-- If `P` is closed under limits of shape `J` in `Comma L R`, then when `D` has
a limit in `Comma L R`, the forgetful functor creates this limit. -/
noncomputable def forgetCreatesColimitOfClosed
    (h : ClosedUnderColimitsOfShape J (fun f : Comma L R ↦ P f.hom))
    [HasColimit (D ⋙ forget L R P ⊤ ⊤)] :
    CreatesColimit D (forget L R P ⊤ ⊤) :=
  createsColimitOfFullyFaithfulOfIso
    (⟨colimit (D ⋙ forget L R P ⊤ ⊤), h.colimit fun j ↦ (D.obj j).prop⟩)
    (Iso.refl _)

/-- If `Comma L R` has colimits of shape `J` and `Comma L R` is closed under colimits of shape
`J`, then `forget L R P ⊤ ⊤` creates colimits of shape `J`. -/
noncomputable def forgetCreatesColimitsOfShapeOfClosed [HasColimitsOfShape J (Comma L R)]
    (h : ClosedUnderColimitsOfShape J (fun f : Comma L R ↦ P f.hom)) :
    CreatesColimitsOfShape J (forget L R P ⊤ ⊤) where
  CreatesColimit := forgetCreatesColimitOfClosed _ _ h

lemma hasColimit_of_closedUnderColimitsOfShape
    (h : ClosedUnderColimitsOfShape J (fun f : Comma L R ↦ P f.hom))
    [HasColimit (D ⋙ forget L R P ⊤ ⊤)] :
    HasColimit D :=
  haveI : CreatesColimit D (forget L R P ⊤ ⊤) := forgetCreatesColimitOfClosed _ D h
  hasColimit_of_created D (forget L R P ⊤ ⊤)

lemma hasColimitsOfShape_of_closedUnderColimitsOfShape [HasColimitsOfShape J (Comma L R)]
    (h : ClosedUnderColimitsOfShape J (fun f : Comma L R ↦ P f.hom)) :
    HasColimitsOfShape J (P.Comma L R ⊤ ⊤) where
  has_colimit _ := hasColimit_of_closedUnderColimitsOfShape _ _ h

end MorphismProperty.Comma
