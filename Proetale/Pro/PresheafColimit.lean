/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.CategoryTheory.Limits.Preserves.Limits
import Proetale.Mathlib.CategoryTheory.Sites.Continuous
import Proetale.Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Proetale.Pro.Basic

/-!
# Presheaf pushforward preserves certain colimit

In this file we show that under certain compactness assumptions,
the presheaf pushforward preserves filtered colimits.

Instead of considering presheafs, we consider arbitrary left Kan extensions.
-/

universe w u

open CategoryTheory MorphismProperty Limits

namespace CategoryTheory

/-- The assumption on `X` is in particular satisfied if `X` is finitely presentable
and `J` is a small filtered category. -/
lemma exists_hom_of_preservesColimit_coyoneda {C : Type*} [Category* C] {J : Type*}
    [Category* J] {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) {X : C}
    [PreservesColimit D (coyoneda.obj (.op X))] (f : X ⟶ c.pt) :
    ∃ (j : J) (p : X ⟶ D.obj j), p ≫ c.ι.app j = f :=
  Types.jointly_surjective_of_isColimit (isColimitOfPreserves (coyoneda.obj (.op X)) hc) f

lemma exists_eq_of_preservesColimit_coyoneda {C : Type*} [Category* C] {J : Type*}
    [Category* J] [IsFiltered J]
    {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) {X : C}
    [PreservesColimit D (coyoneda.obj (.op X))]
    {i j : J} (f : X ⟶ D.obj i) (g : X ⟶ D.obj j) (h : f ≫ c.ι.app i = g ≫ c.ι.app j) :
    ∃ (k : J) (u : i ⟶ k) (v : j ⟶ k), f ≫ D.map u = g ≫ D.map v :=
  (Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (coyoneda.obj (.op X)) hc)).mp h

lemma exists_eq_of_preservesColimit_coyoneda_self {C : Type*} [Category* C] {J : Type*}
    [Category* J] [IsFiltered J] {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) {X : C}
    [PreservesColimit D (coyoneda.obj (.op X))]
    {i : J} (f g : X ⟶ D.obj i) (h : f ≫ c.ι.app i = g ≫ c.ι.app i) :
    ∃ (j : J) (a : i ⟶ j), f ≫ D.map a = g ≫ D.map a := by
  obtain ⟨j, u, v, heq⟩ := exists_eq_of_preservesColimit_coyoneda hc f g h
  use IsFiltered.coeq u v, u ≫ IsFiltered.coeqHom u v
  rw [Functor.map_comp, reassoc_of% heq, ← Functor.map_comp, ← IsFiltered.coeq_condition]
  simp

lemma IsFinitelyPresentable.exists_eq_of_isColimit_self {C : Type*} [Category* C]
    {J : Type w} [SmallCategory J] [IsFiltered J] {D : J ⥤ C} {c : Cocone D}
    (hc : IsColimit c) {X : C} [IsFinitelyPresentable.{w} X]
    {i : J} (f g : X ⟶ D.obj i) (h : f ≫ c.ι.app i = g ≫ c.ι.app i) :
    ∃ (j : J) (a : i ⟶ j), f ≫ D.map a = g ≫ D.map a :=
  exists_eq_of_preservesColimit_coyoneda_self hc _ _ h

section

-- `F` is a presheaf
-- `L` is a continuous functor
variable {C D E A : Type*} [Category* C] [Category* D] [Category* A] [Category* E]
    (L : C ⥤ D) (F : C ⥤ A) [∀ (F : C ⥤ A), L.HasPointwiseLeftKanExtension F]
    (R : E ⥤ D)

variable {J : Type w} [SmallCategory J] (K : J ⥤ C) [IsFiltered J]
variable {c : Cocone (K ⋙ L)} (hc : IsColimit c)

include hc in
lemma final_costructuredArrowLift_of_isFinitelyPresentable
    [∀ X : C, PreservesColimit (K ⋙ L) (coyoneda.obj (.op <| L.obj X))] [L.Full] [L.Faithful] :
    (CostructuredArrow.lift _ c.ι).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro d
    obtain ⟨j, p, hp⟩ := exists_hom_of_preservesColimit_coyoneda hc d.hom
    use j
    exact ⟨CostructuredArrow.homMk (L.preimage p)⟩
  · intro d j s s'
    obtain ⟨k, a, heq⟩ := exists_eq_of_preservesColimit_coyoneda_self hc (L.map s.left)
        (L.map s'.left) <| by
      trans d.hom
      · simpa using CostructuredArrow.w s
      · simpa using (CostructuredArrow.w s').symm
    refine ⟨k, a, ?_⟩
    ext
    exact L.map_injective (by simpa using heq)

variable [∀ X : C, PreservesColimit (K ⋙ L) (coyoneda.obj (.op <| L.obj X))] [L.Full] [L.Faithful]

include hc in
lemma hasColimit_of_isFinitelyPresentable : HasColimit (K ⋙ F) := by
  rw [← CostructuredArrow.lift_forget _ c.ι]
  suffices HasColimit (CostructuredArrow.lift K c.ι ⋙ CostructuredArrow.proj L c.pt ⋙ F) by
    exact hasColimit_of_iso (Functor.associator _ _ _)
  have := final_costructuredArrowLift_of_isFinitelyPresentable _ _ hc
  exact Functor.Final.comp_hasColimit _

variable (c) in
@[simps]
noncomputable def cocone : Cocone (K ⋙ F) where
  pt := (L.leftKanExtension F).obj c.pt
  ι :=
    Functor.whiskerLeft K (L.leftKanExtensionUnit F) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight c.ι _ ≫
    (Functor.constComp _ _ _).hom

include L F

noncomputable def isColimitCocone : IsColimit (cocone L F K c) := by
  have : HasColimit (K ⋙ F) := hasColimit_of_isFinitelyPresentable _ _ _ hc
  have : HasColimit ((CostructuredArrow.lift K c.ι ⋙ CostructuredArrow.proj L c.pt) ⋙ F) := this
  have := final_costructuredArrowLift_of_isFinitelyPresentable _ _ hc
  let e : colimit (K ⋙ F) ⟶ _ :=
    (HasColimit.isoOfNatIso
      (Functor.associator (CostructuredArrow.lift K c.ι) (CostructuredArrow.proj L c.pt) _)).hom ≫
      colimit.pre _ _ ≫
      (Functor.leftKanExtensionObjIsoColimit L F c.pt).inv
  have heq : e = colimit.desc _ (cocone L F K c) :=
    colimit.hom_ext fun j ↦ by simp [e]
  suffices IsIso (colimit.desc _ (cocone L F K c)) by
    convert IsColimit.ofPointIso (colimit.isColimit <| K ⋙ F)
    assumption
  rw [← heq]
  infer_instance

instance : PreservesColimit (K ⋙ L) (L.leftKanExtension F) := by
  constructor
  intro c hc
  let natIso : K ⋙ L ⋙ L.leftKanExtension F ≅ K ⋙ F :=
    Functor.isoWhiskerLeft K (asIso <| (L.lanAdjunction A).unit.app F).symm
  refine ⟨?_⟩
  refine IsColimit.equivOfNatIsoOfIso natIso.symm (cocone L F K c)
      ((L.leftKanExtension F).mapCocone c) ?_ ?_
  · refine Cocones.ext (Iso.refl _) ?_
    intro j
    simp [natIso]
    rfl
  · exact isColimitCocone _ _ _ hc

end

end CategoryTheory
