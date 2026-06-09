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

section CostructuredArrow

variable {A : Type*} [Category A] {L : A ⥤ T}

/-- A variant of `CategoryTheory.CostructuredArrow.closedUnderLimitsOfShape_walkingCospan`
that only requires `P.IsStableUnderBaseChangeAlong` for the cospan legs of each cone, rather
than the global `P.IsStableUnderBaseChange`. -/
lemma CostructuredArrow.closedUnderLimitsOfShape_walkingCospan_of_baseChangeAlong
    [HasPullbacks A] [HasPullbacks T] [PreservesLimitsOfShape WalkingCospan L] (X : T)
    [P.IsStableUnderComposition] [P.HasOfPostcompProperty P]
    (hbc : ∀ {Y₁ Y₂ : CostructuredArrow L X} (_ : P Y₁.hom) (_ : P Y₂.hom) (f : Y₁ ⟶ Y₂),
        P.IsStableUnderBaseChangeAlong (L.map f.left)) :
    (P.costructuredArrowObj L (X := X)).IsClosedUnderLimitsOfShape WalkingCospan where
  limitsOfShape_le := by
    rintro Y ⟨pres, hpres⟩
    have h : IsPullback (L.map (pres.π.app .left).left) (L.map (pres.π.app .right).left)
        (L.map (pres.diag.map WalkingCospan.Hom.inl).left)
        (L.map (pres.diag.map WalkingCospan.Hom.inr).left) :=
      IsPullback.of_isLimit_cone <| isLimitOfPreserves
        (CategoryTheory.CostructuredArrow.toOver L X ⋙ CategoryTheory.Over.forget X) pres.isLimit
    have hY : Y.hom = L.map (pres.π.app .left).left ≫ (pres.diag.obj .left).hom := by simp
    have := hbc (hpres .left) (hpres .one) (pres.diag.map WalkingCospan.Hom.inl)
    rw [MorphismProperty.costructuredArrowObj_iff, hY]
    refine P.comp_mem _ _ ?_ (hpres _)
    refine MorphismProperty.IsStableUnderBaseChangeAlong.of_isPullback h.flip ?_
    exact P.of_postcomp _ (pres.diag.obj WalkingCospan.one).hom (hpres .one)
      (by simpa using hpres .right)

end CostructuredArrow

section Over

variable {X : T}

/-- A variant of `CategoryTheory.Over.closedUnderLimitsOfShape_pullback` that only requires
`P.IsStableUnderBaseChangeAlong` for the cospan legs of each cone, rather than the global
`P.IsStableUnderBaseChange`. -/
lemma Over.closedUnderLimitsOfShape_walkingCospan_of_baseChangeAlong [HasPullbacks T]
    [P.IsStableUnderComposition] [P.HasOfPostcompProperty P]
    (hbc : ∀ {Y₁ Y₂ : Over X} (_ : P Y₁.hom) (_ : P Y₂.hom) (f : Y₁ ⟶ Y₂),
        P.IsStableUnderBaseChangeAlong f.left) :
    (P.overObj (X := X)).IsClosedUnderLimitsOfShape WalkingCospan :=
  CostructuredArrow.closedUnderLimitsOfShape_walkingCospan_of_baseChangeAlong (L := 𝟭 T) P X hbc

end Over

end CategoryTheory
