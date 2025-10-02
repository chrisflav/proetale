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

end Comma

/-- `P` is stable under colimits of shape `J` if `P` holds for the induced morphism
`colim Dᵢ ⟶ X` if every `Dᵢ ⟶ X` satisfies `P`. -/
def StableUnderColimitsOfShape (J : Type*) [Category J] (P : MorphismProperty T) : Prop :=
  ∀ {D : J ⥤ T} (c : Cocone D) (hc : IsColimit c) {X : T}
    (s : D ⟶ (Functor.const J).obj X),
    (∀ j, P (s.app j)) → P (hc.desc (Cocone.mk X s))

lemma StableUnderColimitsOfShape.mk {J : Type*} [Category J] {P : MorphismProperty T}
    [P.RespectsIso]
    (c : ∀ (D : J ⥤ T) [HasColimit D], Cocone D)
    (hc : ∀ (D : J ⥤ T) [HasColimit D], IsColimit (c D))
    (H : ∀ (D : J ⥤ T) [HasColimit D] {X : T} (s : D ⟶ (Functor.const J).obj X),
      (∀ j, P (s.app j)) → P ((hc D).desc (Cocone.mk X s))) :
    P.StableUnderColimitsOfShape J := by
  intro D d hd X s hs
  have : HasColimit D := hd.hasColimit
  rw [← hd.coconePointUniqueUpToIso_hom_desc (hc D), P.cancel_left_of_respectsIso]
  exact H _ _ hs

variable {C : Type*} [Category C] (F : C ⥤ T)

lemma StableUnderColimitsOfShape.closedUnderColimitsOfShape'
    {J : Type*} [Category J] {P : MorphismProperty T}
    (hP : P.StableUnderColimitsOfShape J) (X : T) [HasColimitsOfShape J C]
    [PreservesColimitsOfShape J F] :
    ClosedUnderColimitsOfShape J (fun Y : CostructuredArrow F X ↦ P Y.hom) := by
  intro D c hc hD
  let D' : J ⥤ T := D ⋙ CategoryTheory.CostructuredArrow.proj F X ⋙ F
  let c' : Cocone D' := Functor.mapCocone _ c
  let hc' : IsColimit c' := isColimitOfPreserves _ hc
  let s : D' ⟶ (Functor.const J).obj X := { app j := (D.obj j).hom }
  dsimp at hD
  convert hP (D := D') c' hc' (X := X) s hD
  apply hc'.hom_ext
  intro j
  simp only [Functor.const_obj_obj, IsColimit.fac]
  simp [c', s]

lemma StableUnderColimitsOfShape.closedUnderColimitsOfShape
    {J : Type*} [Category J] {P : MorphismProperty T}
    (hP : P.StableUnderColimitsOfShape J) (X : T) [HasColimitsOfShape J T] :
    ClosedUnderColimitsOfShape J (fun Y : Over X ↦ P Y.hom) :=
  StableUnderColimitsOfShape.closedUnderColimitsOfShape' _ hP _

lemma StableUnderColimitsOfShape.iff_closedUnderColimitsOfShape {J : Type*} [Category J]
    {P : MorphismProperty T} [HasColimitsOfShape J T] :
    P.StableUnderColimitsOfShape J ↔
      ∀ X, ClosedUnderColimitsOfShape J (fun Y : Over X ↦ P Y.hom) := by
  refine ⟨fun hP X ↦ hP.closedUnderColimitsOfShape _, fun hP ↦ ?_⟩
  intro D c hc X s hs
  let D' : J ⥤ Over X :=
  { obj j := CategoryTheory.Over.mk (s.app j)
    map {i j} f := CategoryTheory.Over.homMk (D.map f) }
  let c' : Cocone D' :=
  { pt := CategoryTheory.Over.mk (hc.desc { pt := X, ι := s })
    ι.app j := CategoryTheory.Over.homMk (c.ι.app j) }
  let hc' : IsColimit c' :=
    isColimitOfReflects (CategoryTheory.Over.forget X) hc
  exact (hP X) hc' hs

variable (J : Type*) [Category J] (P : MorphismProperty T)
  (hP : P.StableUnderColimitsOfShape J) (X : T)

noncomputable instance [HasColimitsOfShape J T] : CreatesColimitsOfShape J (MorphismProperty.Over.forget P ⊤ X) :=
  Comma.forgetCreatesColimitsOfShapeOfClosed _ (hP.closedUnderColimitsOfShape X)

instance [HasColimitsOfShape J T] : HasColimitsOfShape J (P.Over ⊤ X) :=
  Comma.hasColimitsOfShape_of_closedUnderColimitsOfShape _ (hP.closedUnderColimitsOfShape X)

variable [HasColimitsOfShape J C] [PreservesColimitsOfShape J F]

noncomputable instance :
    CreatesColimitsOfShape J (MorphismProperty.CostructuredArrow.forget P ⊤ F X) :=
  Comma.forgetCreatesColimitsOfShapeOfClosed _ (hP.closedUnderColimitsOfShape' _ X)

include hP in
lemma CostructuredArrow.hasColimitsOfShape : HasColimitsOfShape J (P.CostructuredArrow ⊤ F X) :=
  Comma.hasColimitsOfShape_of_closedUnderColimitsOfShape _ (hP.closedUnderColimitsOfShape' _ X)

end MorphismProperty

end CategoryTheory
