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

@[upstreamed mathlib 3145]
instance GrothendieckTopology.preservesLimitsOfShape_yoneda (J : GrothendieckTopology C)
    [J.Subcanonical] {I : Type*} [Category I] :
    PreservesLimitsOfShape I J.yoneda :=
  have : PreservesLimitsOfShape I (J.yoneda ⋙ sheafToPresheaf J _) :=
    inferInstanceAs <| PreservesLimitsOfShape I CategoryTheory.yoneda
  CategoryTheory.Limits.preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf J _)

variable (J : GrothendieckTopology C) [J.Subcanonical]
variable {ι : Type*} (X : ι → C)
variable {c : Cofan X} (hc : IsColimit c) (H : (Sieve.ofArrows _ c.inj) ∈ J c.pt)

lemma Limits.IsTerminal.subsingleton_forget [HasForget C]
    [PreservesLimit (Functor.empty.{0} C) (forget C)]
    {X : C} (h : IsTerminal X) :
    Subsingleton ((forget C).obj X) :=
  (Types.isTerminalEquivIsoPUnit _ <| h.isTerminalObj (forget C) X).toEquiv.subsingleton

@[upstreamed mathlib 3145]
lemma eq_of_eq
    (s : Cofan fun i ↦ J.yoneda.obj (X i))
    {Y : C} {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (hab : a ≫ c.inj i = b ≫ c.inj j)
    [∀ i, Mono (c.inj i)]
    (Hdisj : ∀ {i j : ι} (_ : i ≠ j) {Y : C} (a : Y ⟶ X i)
      (b : Y ⟶ X j) (_ : a ≫ c.inj i = b ≫ c.inj j), Nonempty (IsInitial Y))
    (hempty : (Y : C) → IsInitial Y → ⊥ ∈ J Y) :
    (s.inj i).val.app (op Y) a = (s.inj j).val.app (op Y) b := by
  by_cases h : i = j
  · subst h
    obtain rfl := (cancel_mono _).mp hab
    rfl
  · obtain ⟨h⟩ := Hdisj h a b hab
    exact (Sheaf.isTerminalOfBotCover s.pt _ (hempty Y h)).subsingleton_forget.elim _ _

@[upstreamed mathlib 3145]
noncomputable
def isColimit_cofanMk_yoneda
    [∀ (i : ι), Mono (c.inj i)]
    (hempty : (Y : C) → IsInitial Y → ⊥ ∈ J Y)
    (Hdisj : ∀ {i j : ι} (_ : i ≠ j) {Y : C} (a : Y ⟶ X i)
    (b : Y ⟶ X j), a ≫ c.inj i = b ≫ c.inj j → Nonempty (IsInitial Y)) :
    IsColimit (Cofan.mk _ fun i ↦ J.yoneda.map (c.inj i)) := by
  refine mkCofanColimit _ (fun s ↦ ⟨?_⟩) (fun s j ↦ ?_) fun s m hm ↦ ?_
  · refine (s.pt.2.isSheafFor (Sieve.ofArrows _ c.inj) H).extend ?_
    refine ⟨fun Y g ↦ ((s.inj (Sieve.ofArrows.i g.2)).val.app Y) (Sieve.ofArrows.h g.2), ?_⟩
    · intro ⟨Y⟩ ⟨Z⟩ ⟨(g : Z ⟶ Y)⟩
      ext u
      simp only [Sieve.functor_obj, Sieve.generate_apply, GrothendieckTopology.yoneda_obj_val,
        types_comp_apply, Sieve.functor_map_coe]
      rw [← eq_of_eq (J := J) _ s (g ≫ Sieve.ofArrows.h u.2)
        (Sieve.ofArrows.h <| Sieve.downward_closed _ u.2 g) (by simp) Hdisj hempty]
      apply congrFun ((s.inj _).val.naturality g.op)
  · ext : 1
    let u (j : ι) : yoneda.obj (X j) ⟶ (Sieve.ofArrows _ c.inj).functor :=
      (Sieve.ofArrows _ c.inj).toFunctor (c.inj j) (Sieve.ofArrows_mk _ _ j)
    have (j : ι) : u j ≫ (Sieve.ofArrows _ c.inj).functorInclusion = yoneda.map (c.inj j) :=
      rfl
    simp only [GrothendieckTopology.yoneda_obj_val, Cofan.mk_pt, cofan_mk_inj, Sieve.functor_obj,
      Sieve.generate_apply, Sheaf.comp_val, GrothendieckTopology.yoneda_map_val, ← this,
      Category.assoc, Presieve.IsSheafFor.functorInclusion_comp_extend]
    ext Z (g : Z.unop ⟶ X j)
    have h : Sieve.ofArrows X c.inj (g ≫ c.inj j) :=
      Sieve.downward_closed _ (Sieve.ofArrows_mk _ _ j) _
    exact eq_of_eq (J := J) _ s (Sieve.ofArrows.h h) g (by simp) Hdisj hempty
  · ext : 1
    dsimp only [Cofan.mk_pt, GrothendieckTopology.yoneda_obj_val, id_eq, Sieve.functor_obj,
      Sieve.generate_apply]
    apply Presieve.IsSheafFor.unique_extend
    ext Y ⟨g, hg⟩
    simp [← hm (Sieve.ofArrows.i hg)]

end CategoryTheory
