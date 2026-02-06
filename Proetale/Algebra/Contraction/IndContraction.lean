/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten, Andrew Yang
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Proetale.Mathlib.CategoryTheory.MorphismProperty.IndSpreads

/-!
# Ind contraction
-/

universe v u

namespace CategoryTheory.MorphismProperty

open Limits

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)

alias exists_isPushout := PreIndSpreads.exists_isPushout

namespace IndContraction

variable {C : Type u} [Category.{v} C] (P Q : MorphismProperty C) (X : C)

lemma isFiltered_costructuredArrow_forget' [HasPushouts C]
    [P.IsMultiplicative] [P.IsStableUnderCobaseChange] [HasCoequalizers (P.Under ⊤ X)]
    [PreservesColimitsOfShape WalkingParallelPair (Under.forget P ⊤ X)]
    {S : Under X} :
    IsFiltered (CostructuredArrow (Under.forget P ⊤ X) S) := by
  have : Nonempty (CostructuredArrow (Under.forget P ⊤ X) S) := by
    constructor
    fapply CategoryTheory.CostructuredArrow.mk
    · exact (Under.mk ⊤ (𝟙 X) (P.id_mem X))
    · fapply CategoryTheory.Under.homMk
      exact S.hom
      simp
  have : IsFilteredOrEmpty (CostructuredArrow (Under.forget P ⊤ X) S) := by
    refine ⟨fun u v ↦ ⟨?_, ?_, ?_, trivial⟩, fun u v f g ↦ ?_⟩
    · fapply CategoryTheory.CostructuredArrow.mk
      · apply Under.mk ⊤ (u.left.hom ≫ pushout.inl u.left.hom v.left.hom)
          (P.comp_mem _ _ u.left.2 (P.pushout_inl _ _ v.left.2))
      · fapply CategoryTheory.Under.homMk
        · fapply pushout.desc
          · exact u.hom.right
          · exact v.hom.right
          · simp
        · simp
    · fapply CategoryTheory.CostructuredArrow.homMk
      fapply Under.homMk
      · exact pushout.inl _ _
      · simp
      · simp
      · ext
        simp
    · fapply CategoryTheory.CostructuredArrow.homMk
      fapply Under.homMk
      · exact pushout.inr _ _
      · simp [pushout.condition]
      · simp
      · ext
        simp
    · refine ⟨?_, ?_, ?_⟩
      · fapply CategoryTheory.CostructuredArrow.mk
        · exact coequalizer f.left g.left
        · let hc : IsColimit ((Under.forget P ⊤ X).mapCocone (coequalizer.cofork f.left g.left)) :=
            isColimitOfPreserves _ <| colimit.isColimit (parallelPair f.left g.left)
          let s : Cocone (parallelPair f.left g.left ⋙ Under.forget P ⊤ X) := {
            pt := S
            ι.app x := match x with
              | .zero => u.hom
              | .one => v.hom
            ι.naturality i j t := by
              rcases t
              · simpa using u.w _
              · simpa using u.w _
              · simp
          }
          exact hc.desc s
      · fapply CategoryTheory.CostructuredArrow.homMk
        · apply coequalizer.π
        · show (Under.forget P ⊤ X).map _ ≫ _ = _
          apply
            (isColimitOfPreserves (Under.forget P ⊤ X)
            (colimit.isColimit (parallelPair f.left g.left))).fac
      · ext : 1
        exact coequalizer.condition _ _
  constructor

lemma isFiltered_costructuredArrow_forget [HasPushouts C] [P.IsMultiplicative]
    [P.IsStableUnderCobaseChange] [HasCoequalizers (P.Under ⊤ X)]
    {S : Under X} (hS : IsTerminal S) :
    IsFiltered (CostructuredArrow (Under.forget P ⊤ X) S) := by
  have : Nonempty (CostructuredArrow (Under.forget P ⊤ X) S) :=
    ⟨CategoryTheory.CostructuredArrow.mk (hS.from ((Under.forget P ⊤ X).obj
      (Under.mk ⊤ (𝟙 X) (P.id_mem X))))⟩
  have : IsFilteredOrEmpty (CostructuredArrow (Under.forget P ⊤ X) S) := by
    refine ⟨fun u v ↦ ⟨?_, ?_, ?_, trivial⟩, fun u v f g ↦ ?_⟩
    · exact CategoryTheory.CostructuredArrow.mk <| hS.from
        ((Under.forget P ⊤ X).obj <| Under.mk ⊤ (u.left.hom ≫ pushout.inl u.left.hom v.left.hom)
          (P.comp_mem _ _ u.left.2 (P.pushout_inl _ _ v.left.2)))
    · apply CategoryTheory.CostructuredArrow.homMk
      · apply hS.hom_ext
      · exact Under.homMk (pushout.inl _ _)
    · apply CategoryTheory.CostructuredArrow.homMk
      · apply hS.hom_ext
      · exact Under.homMk (pushout.inr _ _) (by simp [pushout.condition])
    · refine ⟨?_, ?_, ?_⟩
      · apply CategoryTheory.CostructuredArrow.mk
        · exact hS.from _
        · exact coequalizer f.left g.left
      · apply CategoryTheory.CostructuredArrow.homMk
        · apply hS.hom_ext
        · exact coequalizer.π f.left g.left
      · simpa using coequalizer.condition f.left g.left
  constructor

variable [(Under.forget P ⊤ X).HasLeftKanExtension (Under.forget P ⊤ X)]

variable (R) in
noncomputable
def indContraction :
    Under X ⥤ Under X :=
  (Under.forget P ⊤ X).leftKanExtension (Under.forget P ⊤ X)

variable [(Under.forget P ⊤ X).HasPointwiseLeftKanExtension (Under.forget P ⊤ X)]

variable {X} in
noncomputable
def indContractionCocone (S : Under X) :
    Cocone (CostructuredArrow.proj (Under.forget P ⊤ X) S ⋙
      (Under.forget P ⊤ X)) where
  pt := (indContraction P X).obj S
  ι := (colimit.cocone _).ι ≫ (Functor.const _).map
    (CategoryTheory.Functor.leftKanExtensionObjIsoColimit _ _ _).inv

variable {X} in
noncomputable
def isColimitIndContractionCocone (S : Under X) :
    IsColimit (indContractionCocone P S) :=
  .ofIsoColimit (colimit.isColimit _)
    (Cocones.ext (CategoryTheory.Functor.leftKanExtensionObjIsoColimit _ _ _).symm)

variable {X} in
noncomputable
def fromIndContraction (S : Under X) : (indContraction P X).obj S ⟶ S :=
  letI c : Cocone (CostructuredArrow.proj (Under.forget P ⊤ X) S ⋙
      (Under.forget P ⊤ X)) :=
    { pt := S
      ι.app Y := Y.hom
      ι.naturality i j f := by simpa using f.w }
  (isColimitIndContractionCocone P S).desc c

@[simp]
lemma ι_fromIndContraction (S : Under X)
    (Y : CostructuredArrow (Under.forget P ⊤ X) S) :
    (indContractionCocone P S).ι.app Y ≫ fromIndContraction P S = Y.hom :=
  (isColimitIndContractionCocone P S).fac _ _

/-- The `P`-ind contraction of `X ⟶ S` is ind-`P` over `X`. -/
lemma property_indContraction_hom (S : Under X) : P.ind ((indContraction P X).obj S).hom :=
  sorry

lemma exists_costructuredArrow_aux [HasPushouts C] [IndSpreads P]
    {S : Under X} (hS : ∀ {T : Under X} (g : S ⟶ T), P g.right → Q g.right →
      ∃ (s : T ⟶ S), g ≫ s = 𝟙 S)
    [P.IsMultiplicative] [P.IsStableUnderCobaseChange] [Q.IsStableUnderCobaseChange]
    {T : Under X}
    (f : (indContraction P X).obj S ⟶ T)
    (hPf : P f.right)
    (hQf : Q f.right)
    (j : CostructuredArrow (Under.forget P ⊤ X) S)
    (T' : C)
    (f' : ((CostructuredArrow.proj _ _ ⋙ Under.forget P ⊤ X) ⋙ CategoryTheory.Under.forget X).obj j ⟶ T')
    (g : T' ⟶ T.right)
    (h : IsPushout ((indContractionCocone P S).ι.app j).right f' f.right g)
    (hf' : P f') :
    ∃ (T'' : CostructuredArrow (Under.forget P ⊤ X) S), T''.left.right = T' := by
  let c := ((CategoryTheory.Under.forget X).mapCocone (indContractionCocone P S))
  let Pt : Under X :=
    CategoryTheory.Under.mk (T.hom ≫ pushout.inl f.right (fromIndContraction P S).right)
  let gu : S ⟶ Pt := CategoryTheory.Under.homMk (pushout.inr _ _)
    (by
      rw [← CategoryTheory.Under.w (fromIndContraction P S), Category.assoc]
      simp [← pushout.condition, Pt])
  obtain ⟨su, hsu⟩ := hS gu (P.pushout_inr _ _ hPf) (Q.pushout_inr _ _ hQf)
  let T'' : CostructuredArrow (Under.forget P ⊤ X) S :=
      ⟨MorphismProperty.Under.mk ⊤ (j.1.hom ≫ f') (P.comp_mem _ _ j.1.2 hf'), ⟨⟨⟩⟩,
      CategoryTheory.Under.homMk g (by simp [← h.w]) ≫
        CategoryTheory.Under.homMk (pushout.inl _ _) rfl ≫ su⟩
  use T''
  rfl

end IndContraction

end MorphismProperty

end CategoryTheory
