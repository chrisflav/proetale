/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten, Andrew Yang
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
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
  have : Nonempty (CostructuredArrow (Under.forget P ⊤ X) S) :=
    ⟨CategoryTheory.CostructuredArrow.mk
      (show (Under.forget P ⊤ X).obj (Under.mk ⊤ (𝟙 X) (P.id_mem X)) ⟶ S from
        CategoryTheory.Under.homMk S.hom (by exact Category.id_comp _))⟩
  have : IsFilteredOrEmpty (CostructuredArrow (Under.forget P ⊤ X) S) := by
    refine ⟨fun u v ↦ ⟨?_, ?_, ?_, trivial⟩, fun u v f g ↦ ?_⟩
    · -- Common upper bound: pushout in C, with descent to S via pushout.desc
      have hu := CategoryTheory.Under.w u.hom
      have hv := CategoryTheory.Under.w v.hom
      -- hu : ((Under.forget P ⊤ X).obj u.left).hom ≫ u.hom.right = S.hom
      -- hv : ((Under.forget P ⊤ X).obj v.left).hom ≫ v.hom.right = S.hom
      -- ((Under.forget P ⊤ X).obj u.left).hom = u.left.hom definitionally
      have hcompat : u.left.hom ≫ u.hom.right = v.left.hom ≫ v.hom.right := by
        change ((Under.forget P ⊤ X).obj u.left).hom ≫ _ =
          ((Under.forget P ⊤ X).obj v.left).hom ≫ _
        rw [hu]; exact hv.symm
      have hw : (u.left.hom ≫ pushout.inl u.left.hom v.left.hom) ≫
          pushout.desc u.hom.right v.hom.right hcompat = S.hom := by
        rw [Category.assoc, pushout.inl_desc]; exact hu
      exact CategoryTheory.CostructuredArrow.mk
        (show (Under.forget P ⊤ X).obj (Under.mk ⊤
            (u.left.hom ≫ pushout.inl u.left.hom v.left.hom)
            (P.comp_mem _ _ u.left.2 (P.pushout_inl _ _ v.left.2))) ⟶ S from
          CategoryTheory.Under.homMk (pushout.desc u.hom.right v.hom.right hcompat) hw)
    · -- Morphism from u to the upper bound
      exact CategoryTheory.CostructuredArrow.homMk (Under.homMk (pushout.inl _ _))
        (by ext; exact pushout.inl_desc _ _ _)
    · -- Morphism from v to the upper bound
      exact CategoryTheory.CostructuredArrow.homMk
        (Under.homMk (pushout.inr _ _) (pushout.condition ..).symm)
        (by ext; exact pushout.inr_desc _ _ _)
    · -- Coequalizer: use coequalizer in P.Under ⊤ X, preserved by Under.forget
      have hcoeq : IsColimit (Cofork.ofπ
          ((Under.forget P ⊤ X).map (coequalizer.π f.left g.left))
          (by simp only [← Functor.map_comp]; congr 1; exact coequalizer.condition f.left g.left) :
          Cofork ((Under.forget P ⊤ X).map f.left) ((Under.forget P ⊤ X).map g.left)) :=
        isColimitCoforkMapOfIsColimit (Under.forget P ⊤ X)
          (coequalizer.condition f.left g.left) (coequalizerIsCoequalizer f.left g.left)
      -- v.hom coequalizes the images since f and g are parallel CostructuredArrow morphisms
      have hv : (Under.forget P ⊤ X).map f.left ≫ v.hom =
          (Under.forget P ⊤ X).map g.left ≫ v.hom := by
        rw [CostructuredArrow.w f, CostructuredArrow.w g]
      refine ⟨?_, ?_, ?_⟩
      · exact CategoryTheory.CostructuredArrow.mk (Cofork.IsColimit.desc hcoeq v.hom hv)
      · refine CategoryTheory.CostructuredArrow.homMk (coequalizer.π f.left g.left) ?_
        -- Goal: (Under.forget P ⊤ X).map (coequalizer.π f.left g.left) ≫ (mk desc).hom = v.hom
        -- This is definitionally (Cofork.ofπ ...).π ≫ desc = v.hom
        exact Cofork.IsColimit.π_desc' hcoeq v.hom hv
      · simpa using coequalizer.condition f.left g.left
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
      · exact Under.homMk (pushout.inr _ _) (pushout.condition ..).symm
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
  -- Step 1: Set up notation
  set ι_j := ((indContractionCocone P S).ι.app j).right
  -- ι_j is the right component of the cocone leg at j
  -- Step 2: Key fact about ι_j composed with fromIndContraction
  have hι_from : ι_j ≫ (fromIndContraction P S).right = j.hom.right :=
    congrArg CommaMorphism.right (ι_fromIndContraction P X S j)
  -- Step 3: The "small" pushout of j.hom.right and f'
  have hSmall : IsPushout j.hom.right f'
      (pushout.inl j.hom.right f') (pushout.inr j.hom.right f') :=
    IsPushout.of_hasPushout j.hom.right f'
  -- Step 4: Compatibility for the desc map
  have hcompat_desc : ι_j ≫ ((fromIndContraction P S).right ≫ pushout.inl j.hom.right f')
      = f' ≫ pushout.inr j.hom.right f' := by
    rw [← Category.assoc, hι_from]; exact pushout.condition ..
  -- Step 5: Construct comparison map T.right → pushout(j.hom.right, f')
  let comparison := h.desc ((fromIndContraction P S).right ≫ pushout.inl j.hom.right f')
      (pushout.inr j.hom.right f') hcompat_desc
  have hcomp_inl : f.right ≫ comparison =
      (fromIndContraction P S).right ≫ pushout.inl j.hom.right f' := h.inl_desc _ _ _
  have hcomp_inr : g ≫ comparison = pushout.inr j.hom.right f' := h.inr_desc _ _ _
  -- Step 6: The outer rectangle is a pushout
  have hOuter : IsPushout (ι_j ≫ (fromIndContraction P S).right) f'
      (pushout.inl j.hom.right f') (g ≫ comparison) := by
    rw [hι_from, hcomp_inr]; exact hSmall
  -- Step 7: By pasting law, the right square is a pushout
  have hRightPushout : IsPushout (fromIndContraction P S).right f.right
      (pushout.inl j.hom.right f') comparison :=
    IsPushout.of_left hOuter hcomp_inl.symm h
  -- Step 8: Cobase change gives P and Q on pushout.inl
  have hQ_inl : Q (pushout.inl j.hom.right f') := Q.of_isPushout hRightPushout hQf
  have hP_inl : P (pushout.inl j.hom.right f') := P.of_isPushout hRightPushout hPf
  -- Step 9: Apply hS to get a retraction
  obtain ⟨s, hs⟩ := hS (CategoryTheory.Under.homMk (pushout.inl j.hom.right f') :
    S ⟶ CategoryTheory.Under.mk (S.hom ≫ pushout.inl j.hom.right f')) hP_inl hQ_inl
  have hretract : (pushout.inl j.hom.right f') ≫ s.right = 𝟙 S.right := by
    have := congrArg CommaMorphism.right hs; simpa using this
  -- Step 10: Construct φ and prove hφ
  let φ := pushout.inr j.hom.right f' ≫ s.right
  have hcond : j.hom.right ≫ pushout.inl j.hom.right f' = f' ≫ pushout.inr j.hom.right f' :=
    pushout.condition ..
  have hw : j.left.hom ≫ j.hom.right = S.hom := by
    have := CategoryTheory.Under.w j.hom
    exact this
  have hφ : (j.left.hom ≫ f') ≫ φ = S.hom := by
    -- Under.w s : (S.hom ≫ pushout.inl) ≫ s.right = S.hom
    have hs_w : (S.hom ≫ pushout.inl j.hom.right f') ≫ s.right = S.hom :=
      CategoryTheory.Under.w s
    -- hcond reassociated with s.right
    have hcond_reassoc : j.hom.right ≫ pushout.inl j.hom.right f' ≫ s.right =
        f' ≫ pushout.inr j.hom.right f' ≫ s.right := by
      rw [← Category.assoc, ← Category.assoc]; exact congrArg (· ≫ s.right) hcond
    have hcond_reassoc2 : j.left.hom ≫ j.hom.right ≫ pushout.inl j.hom.right f' ≫ s.right =
        j.left.hom ≫ f' ≫ pushout.inr j.hom.right f' ≫ s.right := by
      exact congrArg (j.left.hom ≫ ·) hcond_reassoc
    -- Goal: (j.left.hom ≫ f') ≫ φ = S.hom
    -- Unfold φ and reassociate
    change (j.left.hom ≫ f') ≫ (pushout.inr j.hom.right f' ≫ s.right) = S.hom
    rw [Category.assoc]
    -- Goal: j.left.hom ≫ f' ≫ pushout.inr ≫ s.right = S.hom
    rw [← hcond_reassoc2]
    -- Goal: j.left.hom ≫ (j.hom.right ≫ (pushout.inl ≫ s.right)) = S.hom
    -- Transform to (j.left.hom ≫ j.hom.right) ≫ (pushout.inl ≫ s.right)
    -- then to S.hom ≫ (pushout.inl ≫ s.right) = (S.hom ≫ pushout.inl) ≫ s.right = S.hom
    exact (Category.assoc j.left.hom j.hom.right _).symm.trans
      ((congrArg (· ≫ (pushout.inl j.hom.right f' ≫ s.right)) hw).trans
        ((Category.assoc S.hom _ s.right).symm.trans hs_w))
  -- Step 11: Construct the CostructuredArrow object
  exact ⟨CategoryTheory.CostructuredArrow.mk
    (show (Under.forget P ⊤ X).obj (Under.mk ⊤ (j.left.hom ≫ f')
      (P.comp_mem _ _ j.left.2 hf')) ⟶ S from
      CategoryTheory.Under.homMk φ hφ), rfl⟩

end IndContraction

end MorphismProperty

end CategoryTheory
