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

end CategoryTheory
