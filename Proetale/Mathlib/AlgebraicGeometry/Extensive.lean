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

end CategoryTheory

namespace AlgebraicGeometry

noncomputable
instance : BinaryCoproductsDisjoint Scheme.{u} := by
  refine .mk fun X Y ↦ ?_
  have : Mono (BinaryCofan.mk (coprod.inl (X := X) (Y := Y)) coprod.inr).inl := by
    dsimp
    infer_instance
  have : Mono (BinaryCofan.mk (coprod.inl (X := X) (Y := Y)) coprod.inr).inr := by
    dsimp
    infer_instance
  refine BinaryCoproductDisjoint.of_binaryCofan (c := .mk coprod.inl coprod.inr) ?_
      (pullback.isLimit _ _) ?_
  · exact coprodIsCoprod X Y
  · apply Nonempty.some
    rw [isInitial_iff_isEmpty]
    exact isEmpty_of_commSq_sigmaι_of_ne.{u} (σ := WalkingPair) (g := fun j ↦ j.casesOn X Y)
      (i := .left) (j := .right) ⟨pullback.condition⟩ (by simp)

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
instance : HasSheafify Scheme.zariskiTopology.{u} (Type (u + 1)) := inferInstance

instance : MonoCoprod Scheme.{u} := by
  refine .mk' fun X Y ↦ ⟨BinaryCofan.mk coprod.inl coprod.inr, coprodIsCoprod X Y, ?_⟩
  dsimp
  infer_instance

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
      AffineScheme.forgetToScheme := by
    apply createsColimitOfFullyFaithfulOfIso (.mk (∐ fun i ↦ (K.obj ⟨i⟩).1) inferInstance)
    apply HasColimit.isoOfNatIso
    exact Discrete.natIso fun i ↦ Iso.refl _
  exact createsColimitOfIsoDiagram AffineScheme.forgetToScheme Discrete.natIsoFunctor.symm

instance : FinitaryExtensive AffineScheme.{u} :=
  finitaryExtensive_of_preserves_and_reflects (AffineScheme.forgetToScheme)

end AlgebraicGeometry
