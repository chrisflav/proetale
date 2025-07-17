/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Proetale.Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct
import Proetale.Mathlib.AlgebraicGeometry.Sites.BigZariski
import Proetale.Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Limits.Preserves.Ulift

universe v u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category C] {A B : Type*} [Category A] [Category B]
  (J : GrothendieckTopology C) (F : A ⥤ B) [J.HasSheafCompose F]

instance (K : Type*) [Category K] [PreservesLimitsOfShape K F] [HasLimitsOfShape K A] :
    PreservesLimitsOfShape K (sheafCompose J F) :=
  have : PreservesLimitsOfShape K (sheafCompose J F ⋙ sheafToPresheaf J B) :=
    inferInstanceAs <| PreservesLimitsOfShape K
      (sheafToPresheaf J A ⋙ (Functor.whiskeringRight Cᵒᵖ A B).obj F)
  CategoryTheory.Limits.preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf J B)

@[simp]
lemma Presieve.isSheafFor_comp_uliftFunctor_iff {F : Cᵒᵖ ⥤ Type u} {X : C} {R : Presieve X} :
    R.IsSheafFor (F ⋙ uliftFunctor.{v}) ↔ R.IsSheafFor F := by
  rw [Presieve.IsSheafFor, Presieve.IsSheafFor]
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · let x' : R.FamilyOfElements (F ⋙ uliftFunctor.{v}) := fun Y f hf ↦ ⟨x f hf⟩
    have hx' : x'.Compatible := by
      introv Y₁ h
      simp [x', hx g₁ g₂ h₁ h₂ h]
    obtain ⟨t, ht, huniq⟩ := h _ hx'
    refine ⟨t.down, ?_, ?_⟩
    · intro Y g hg
      exact Equiv.ulift.symm.injective (ht g hg)
    · intro t' ht'
      exact Equiv.ulift.symm.injective (huniq _ fun Y g hg ↦ Equiv.ulift.injective (ht' g hg))
  · let x' : R.FamilyOfElements F := fun Y f hf ↦ (x f hf).down
    have hx' : x'.Compatible := by
      introv Y₁ h
      simpa [x'] using hx g₁ g₂ h₁ h₂ h
    obtain ⟨t, ht, huniq⟩ := h _ hx'
    refine ⟨⟨t⟩, ?_, ?_⟩
    · intro Y g hg
      exact Equiv.ulift.injective (ht g hg)
    · intro t' ht'
      exact Equiv.ulift.injective (huniq _ fun Y g hg ↦ Equiv.ulift.symm.injective (ht' g hg))

@[simp]
lemma Presieve.isSheaf_comp_uliftFunctor_iff {F : Cᵒᵖ ⥤ Type u} :
    IsSheaf J (F ⋙ uliftFunctor.{v}) ↔ IsSheaf J F := by
  simp [IsSheaf, Presieve.isSheafFor_comp_uliftFunctor_iff]

end CategoryTheory

namespace AlgebraicGeometry

noncomputable
instance : CoproductsDisjoint Scheme.{u} where
  CoproductDisjoint X Y := by
    have : Mono (BinaryCofan.mk (coprod.inl (X := X) (Y := Y)) coprod.inr).inl := by
      dsimp
      infer_instance
    have : Mono (BinaryCofan.mk (coprod.inl (X := X) (Y := Y)) coprod.inr).inr := by
      dsimp
      infer_instance
    refine CoproductDisjoint.of_binaryCofan_of_pullbackCone (.mk coprod.inl coprod.inr) ?_ ?_ ?_ ?_
    · exact coprodIsCoprod X Y
    · exact pullback.cone _ _
    · exact pullback.isLimit _ _
    · apply Nonempty.some
      rw [isInitial_iff_isEmpty]
      exact isEmpty_of_commSq_sigmaι_of_ne.{0, u} (ι := WalkingPair) (X := fun j ↦ j.casesOn X Y)
        (i := .left) (j := .right) ⟨pullback.condition⟩ (by simp)

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
instance : HasSheafify Scheme.zariskiTopology.{u} (Type (u + 1)) := inferInstance

instance : MonoCoprod Scheme.{u} := by
  refine .mk' fun X Y ↦ ⟨BinaryCofan.mk coprod.inl coprod.inr, coprodIsCoprod X Y, ?_⟩
  dsimp
  infer_instance

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
/-- One possible proof is to embed into the category of Zariski sheaves. -/
instance : FinitaryExtensive Scheme.{u} := by
  let C := ULiftHom.{u + 1, u + 1} Scheme
  let e : Scheme.{u} ≌ C := ULiftHom.equiv
  let J : GrothendieckTopology C :=
    e.inverse.inducedTopology Scheme.zariskiTopology
  have : J.Subcanonical := by
    refine .of_isSheaf_yoneda_obj _ fun X ↦ ?_
    show Presieve.IsSheaf J ((e.inverse.op ⋙ yoneda.obj X) ⋙ uliftFunctor.{u + 1, u})
    rw [Presieve.isSheaf_comp_uliftFunctor_iff]
    apply Functor.op_comp_isSheaf_of_types e.inverse J (Scheme.zariskiTopology.{u})
      (Scheme.zariskiTopology.yoneda.obj X)
  let F : C ⥤ Sheaf J (Type (u + 1)) := J.yoneda
  have : MonoCoprod C :=
    .monoCoprod_of_preservesCoprod_of_reflectsMono e.inverse
  have {κ : Type} : HasColimitsOfShape (Discrete κ) C :=
    Adjunction.hasColimitsOfShape_of_equivalence e.inverse
  have : PreservesColimitsOfShape (Discrete WalkingPair) F := by
    apply J.preservesColimitsOfShape_yoneda_of_ofArrows_inj_mem
    · intro X c hc
      simp only [C]
      have : Sieve.ofArrows _ (e.inverse.mapCocone c).ι.app ∈
          Scheme.zariskiTopology (e.inverse.mapCocone c).pt :=
        ofArrows_ι_mem_zariskiTopology_of_isColimit _ (isColimitOfPreserves e.inverse hc)
      apply GrothendieckTopology.superset_covering _ _ this
      rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro - - ⟨i⟩
      refine ⟨X i.1, c.ι.app i, 𝟙 _, ?_, rfl⟩
      apply Sieve.ofArrows_mk
    · intro X c hc i j hij (Y : Scheme.{u}) ⟨(a : Y ⟶ X i)⟩ ⟨(b : Y ⟶ X j)⟩
        (hab : e.functor.map a ≫ c.inj i = e.functor.map b ≫ c.inj j)
      constructor
      refine (Limits.IsInitial.isInitialIffObj e.inverse _).invFun (Nonempty.some ?_)
      rw [isInitial_iff_isEmpty]
      refine isEmpty_of_commSq_sigmaι_of_ne (f := a) (g := b) ⟨?_⟩ hij
      let X' : WalkingPair → Scheme.{u} := X
      let iso : colimit (Discrete.functor X' ⋙ e.functor) ≅ c.pt :=
        IsColimit.coconePointsIsoOfNatIso (colimit.isColimit _) hc Discrete.natIsoFunctor
      have this (i) : e.functor.map (Sigma.ι X' i) = c.inj i ≫ iso.inv ≫
          (preservesColimitIso e.functor (Discrete.functor X)).inv := by
        simp only [Cofan.inj, IsColimit.coconePointsIsoOfNatIso_inv, IsColimit.ι_map_assoc,
          Discrete.functor_obj_eq_as, Functor.comp_obj, Discrete.natIsoFunctor_inv_app,
          colimit.cocone_x, colimit.cocone_ι, ι_preservesColimitIso_inv, e, X', iso, C]
        rfl
      apply e.functor.map_injective
      rw [Functor.map_comp, this, Functor.map_comp, this, reassoc_of% hab]
    · intro Y hY
      simp only [Functor.mem_inducedTopology_sieves_iff, Sieve.functorPushforward_bot, J]
      convert Scheme.bot_mem_grothendieckTopology _
      rw [← isInitial_iff_isEmpty]
      exact ⟨hY.isInitialObj e.inverse Y⟩
  apply finitaryExtensive_of_preserves_and_reflects (e.functor ⋙ F)

instance {ι : Type*} [Finite ι] : Finite (Discrete ι) :=
  discreteEquiv.finite_iff.mpr inferInstance

noncomputable instance {ι : Type*} [Small.{u} ι] [Finite ι] :
    CreatesColimitsOfShape (Discrete ι) AffineScheme.forgetToScheme.{u} := by
  let ι' := Shrink.{u} ι
  suffices CreatesColimitsOfShape (Discrete ι') AffineScheme.forgetToScheme.{u} by
    exact createsColimitsOfShapeOfEquiv (Discrete.equivalence (equivShrink ι)).symm
      AffineScheme.forgetToScheme
  refine ⟨fun {K} ↦ ?_⟩
  have : CreatesColimit (Discrete.functor (K.obj ∘ Discrete.mk))
      AffineScheme.forgetToScheme :=
    createsColimitOfFullyFaithfulOfIso (.mk (∐ fun i ↦ (K.obj ⟨i⟩).1) inferInstance) (Iso.refl _)
  exact createsColimitOfIsoDiagram AffineScheme.forgetToScheme Discrete.natIsoFunctor.symm

instance : FinitaryExtensive AffineScheme.{u} :=
  finitaryExtensive_of_preserves_and_reflects (AffineScheme.forgetToScheme)

end AlgebraicGeometry
