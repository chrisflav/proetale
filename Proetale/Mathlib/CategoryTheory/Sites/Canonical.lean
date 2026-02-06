import Upstreamer
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.CategoryTheory.Sites.Subcanonical
import Proetale.Mathlib.CategoryTheory.Sites.EffectiveEpimorphic

universe u

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category C]

lemma Sieve.EffectiveEpimorphic.of_subcanonical (J : GrothendieckTopology C) [J.Subcanonical]
    {X : C} (R : Sieve X) (h : R ∈ J X) :
    R.EffectiveEpimorphic := by
  rw [Sieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
  intro Y
  refine Presieve.IsSheaf.isSheafFor J
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj Y)) _ ?_
  simpa

lemma Presieve.EffectiveEpimorphic.of_subcanonical (J : GrothendieckTopology C) [J.Subcanonical]
    {X : C} (R : Presieve X) (h : Sieve.generate R ∈ J X) :
    R.EffectiveEpimorphic := by
  rw [Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
  intro Y
  exact Presieve.IsSheaf.isSheafFor J
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj Y)) _ h

variable (J : GrothendieckTopology C) [J.Subcanonical]
variable {ι : Type*} (X : ι → C)
variable {c : Cofan X} (hc : IsColimit c) (H : (Sieve.ofArrows _ c.inj) ∈ J c.pt)

lemma Limits.IsTerminal.subsingleton_forget [HasForget C]
    [PreservesLimit (Functor.empty.{0} C) (forget C)]
    {X : C} (h : IsTerminal X) :
    Subsingleton ((forget C).obj X) :=
  (Types.isTerminalEquivIsoPUnit _ <| h.isTerminalObj (forget C) X).toEquiv.subsingleton

end CategoryTheory
