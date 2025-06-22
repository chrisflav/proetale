import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import Mathlib.CategoryTheory.Sites.SheafOfTypes

namespace CategoryTheory

variable {C : Type*} [Category C] {X : C}

lemma Sieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda (S : Sieve X) :
    S.EffectiveEpimorphic ↔ ∀ Y, S.arrows.IsSheafFor (yoneda.obj Y) :=
  S.forallYonedaIsSheaf_iff_colimit.symm

lemma Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda (S : Presieve X) :
    S.EffectiveEpimorphic ↔ ∀ Y, S.IsSheafFor (yoneda.obj Y) := by
  simp_rw [Presieve.isSheafFor_iff_generate S]
  rw [Presieve.EffectiveEpimorphic, Sieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]

end CategoryTheory
