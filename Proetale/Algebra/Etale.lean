/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Proetale.Mathlib.CategoryTheory.MorphismProperty.IndSpreads

/-!
# Etale ind-spreads
-/

universe w u

open TensorProduct CategoryTheory

def Subalgebra.FG.finiteType {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    {A : Subalgebra R S} (h : A.FG) :
    Algebra.FiniteType R A :=
  A.fg_iff_finiteType.mp h

lemma RingHom.FinitePresentation.of_bijective {R S : Type*} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : Function.Bijective f) :
    f.FinitePresentation :=
  .of_surjective f hf.2 <| by
    have : ker f = ⊥ := by
      rw [← RingHom.injective_iff_ker_eq_bot]
      exact hf.1
    rw [this]
    exact Submodule.fg_bot

namespace Algebra

variable (R : Type*) (A : Type u) (B : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B] [Algebra A B]

-- In mathlib PR #32837 by Andrew
lemma Etale.exists_subalgebra_fg [Etale A B] :
    ∃ (A₀ : Subalgebra R A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
      A₀.FG ∧ Etale A₀ B₀ ∧ Nonempty (B ≃ₐ[A] A ⊗[A₀] B₀) :=
  sorry

end Algebra

namespace CommRingCat

def etale : MorphismProperty CommRingCat :=
  RingHom.toMorphismProperty fun f ↦ f.Etale

@[simp]
lemma etale_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    etale f ↔ f.hom.Etale := .rfl

instance : etale.IsStableUnderCobaseChange := by
  rw [etale, RingHom.isStableUnderCobaseChange_toMorphismProperty_iff]
  exact RingHom.Etale.isStableUnderBaseChange

variable {J : Type*} [Category J] (D : J ⥤ CommRingCat.{u})

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
instance : MorphismProperty.PreIndSpreads.{u} etale.{u} := by
  refine .of_isInitial CommRingCat.isInitial fun R S f hf ↦ ?_
  algebraize [f.hom]
  have hf_eq : f = ofHom (algebraMap R S) := rfl
  have : Algebra.Etale R S := hf
  obtain ⟨R₀, S₀, _, _, hfg, h, ⟨e⟩⟩ := Algebra.Etale.exists_subalgebra_fg ℤ R S
  let g : S₀ →+* S := e.symm.toRingHom.comp <| Algebra.TensorProduct.includeRight.toRingHom
  algebraize [g]
  have : IsScalarTower R₀ S₀ ↑S := .of_algebraMap_eq fun x ↦ by
    simpa [RingHom.algebraMap_toAlgebra, g] using (e.symm.toAlgHom.commutes x.val).symm
  refine ⟨.of R₀, .of S₀, CommRingCat.ofHom (algebraMap R₀ R),
      CommRingCat.ofHom g, CommRingCat.ofHom (algebraMap R₀ S₀), ?_, ?_, ?_⟩
  · apply isFinitelyPresentable
    dsimp
    have : isInitial.to (of R₀) = ofHom ((algebraMap ℤ R₀).comp ULift.ringEquiv.toRingHom) :=
      isInitial.hom_ext _ _
    rw [this]
    apply RingHom.FinitePresentation.comp
    · rw [RingHom.finitePresentation_algebraMap, ← Algebra.FinitePresentation.of_finiteType]
      exact hfg.finiteType
    · exact .of_bijective ULift.ringEquiv.bijective
  · simpa [RingHom.etale_algebraMap]
  · rw [hf_eq, ← RingHom.algebraMap_toAlgebra g, isPushout_iff_isPushout]
    exact Algebra.IsPushout.of_equiv (S' := ↑R ⊗[↥R₀] S₀) e.symm rfl

end CommRingCat
