import Mathlib.CategoryTheory.ObjectProperty.Ind
import Proetale.Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct

universe w

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category C] [Category D]

lemma ObjectProperty.ind_iff_of_equivalence (e : C ≌ D) (P : ObjectProperty D)
    [P.IsClosedUnderIsomorphisms] (X : D) :
    ObjectProperty.ind.{w} P X ↔
      ObjectProperty.ind.{w} (P.inverseImage e.functor) (e.inverse.obj X) := by
  dsimp only [ObjectProperty.ind]
  congr!
  refine ⟨fun ⟨pres, h⟩ ↦ ?_, fun ⟨pres, h⟩ ↦ ?_⟩
  · refine ⟨pres.map e.inverse, ?_⟩
    intro i
    simp only [ColimitPresentation.map_diag, Functor.comp_obj,
      ObjectProperty.prop_inverseImage_iff]
    exact P.prop_of_iso ((e.counitIso.app _).symm) (h i)
  · refine ⟨.ofIso (pres.map e.functor) (e.counitIso.app X), fun i ↦ h i⟩

namespace ObjectProperty

lemma ind_inverseImage_le
    {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) (P : ObjectProperty D)
    [PreservesFilteredColimitsOfSize.{w, w} F] :
    ind.{w} (P.inverseImage F) ≤ (ind.{w} P).inverseImage F := by
  intro X ⟨J, _, _, pres, h⟩
  simp only [prop_inverseImage_iff]
  use J, inferInstance, inferInstance, pres.map F, h

lemma ind_inverseImage_eq_of_isEquivalence
    {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    [F.IsEquivalence] :
    ind.{w} (P.inverseImage F) = (ind.{w} P).inverseImage F := by
  refine le_antisymm (ind_inverseImage_le _ _) fun X ⟨J, _, _, pres, h⟩ ↦ ?_
  refine ⟨J, ‹_›, ‹_›, .ofIso (pres.map F.asEquivalence.inverse) ?_, fun j ↦ ?_⟩
  · exact (F.asEquivalence.unitIso.app X).symm
  · exact P.prop_of_iso ((F.asEquivalence.counitIso.app _).symm) (h j)

variable (P : ObjectProperty C)

section Products

lemma ind_pi_of_ind {ι : Type w} [P.IsClosedUnderLimitsOfShape (Discrete ι)]
    [HasProductsOfShape ι C] [IsIPCOfShape.{w} ι C]
    {X : ι → C} (hc : ∀ i, ind.{w} P (X i)) :
    ind.{w} P (∏ᶜ X) := by
  choose J _ _ pres hpres using hc
  use ∀ j, J j, inferInstance, inferInstance
  refine ⟨?_, ?_⟩
  · refine { diag := ?_
             ι := ?_
             isColimit := ?_  }
    · exact Functor.pi (fun i ↦ (pres i).diag) ⋙ Pi.functor _
    · exact (coconePointwiseProduct' fun i ↦ (pres i).cocone).ι
    · exact IsIPCOfShape.isColimitCoconePointwiseProduct' fun i ↦ (pres i).isColimit
  · intro i
    exact P.prop_limit _ fun a ↦ hpres a.1 _

instance isClosedUnderLimitsOfShape_ind_discrete {ι : Type*} [Small.{w} ι] [P.IsClosedUnderLimitsOfShape (Discrete ι)]
    [HasProductsOfShape ι C] [IsIPCOfShape.{w} ι C] :
    (ind.{w} P).IsClosedUnderLimitsOfShape (Discrete ι) := by
  refine .mk' fun X ⟨Y, h⟩ ↦ ?_
  let e := equivShrink ι
  have : HasProductsOfShape (Shrink.{w} ι) C :=
    hasLimitsOfShape_of_equivalence (Discrete.equivalence e)
  have : IsIPCOfShape.{w} (Shrink.{w} ι) C := .of_equiv e
  have : P.IsClosedUnderLimitsOfShape (Discrete (Shrink.{w} ι)) :=
    .of_equivalence (Discrete.equivalence e)
  let iso : limit Y ≅ ∏ᶜ fun i ↦ Y.obj ⟨e.symm i⟩ :=
    (Pi.isoLimit _).symm ≪≫ (Pi.reindex e.symm _).symm
  rw [(ind.{w} P).prop_iff_of_iso iso]
  apply ind_pi_of_ind
  intro i
  apply h

end Products

end ObjectProperty

end CategoryTheory
