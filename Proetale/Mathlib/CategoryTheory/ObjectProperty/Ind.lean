import Mathlib.CategoryTheory.ObjectProperty.Ind

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

end ObjectProperty

end CategoryTheory
