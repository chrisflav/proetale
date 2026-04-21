/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct
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

end CategoryTheory

namespace AlgebraicGeometry

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
