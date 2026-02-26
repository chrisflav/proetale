/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Limits
import Proetale.FromPi1.Etale
import Proetale.Algebra.WeaklyEtale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Weakly étale morphisms

-/

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

/-- A morphism of schemes is said to be weakly étale if it is flat and the diagonal is flat. -/
@[mk_iff]
class WeaklyEtale {X Y : Scheme.{u}} (f : X ⟶ Y) extends Flat f where
  flat_diagonal : Flat (pullback.diagonal f)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

namespace WeaklyEtale

lemma eq_inf :
    @WeaklyEtale = ((@Flat ⊓ MorphismProperty.diagonal @Flat) : MorphismProperty Scheme.{u}) := by
  ext X Y f
  rw [weaklyEtale_iff]
  rfl

instance : RespectsIso @WeaklyEtale := by
  rw [eq_inf]
  infer_instance

instance isStableUnderComposition : IsStableUnderComposition @WeaklyEtale := by
  rw [eq_inf]
  infer_instance

instance isStableUnderBaseChange : IsStableUnderBaseChange @WeaklyEtale := by
  rw [eq_inf]
  infer_instance

instance : IsZariskiLocalAtTarget @WeaklyEtale := by
  rw [eq_inf]
  infer_instance

instance : ContainsIdentities @WeaklyEtale := by
  rw [eq_inf]
  infer_instance

instance : IsMultiplicative @WeaklyEtale where

instance (priority := 900) of_etale [Etale f] : WeaklyEtale f where
  flat_diagonal := inferInstance

instance (priority := 900) etale [WeaklyEtale f] [LocallyOfFinitePresentation f] : Etale f := by
  -- Reduce to the affine case using wlog
  wlog hY : ∃ R, Y = Spec R
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Etale) Y.affineCover]
    intro i
    haveI hw : WeaklyEtale (pullback.snd f (Y.affineCover.f i)) := by
      rw [eq_inf]
      exact ⟨inferInstance,
        MorphismProperty.pullback_snd (P := .diagonal @Flat) _ _ WeaklyEtale.flat_diagonal⟩
    haveI hfp : LocallyOfFinitePresentation (pullback.snd f (Y.affineCover.f i)) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    exact this (pullback.snd _ _) ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Etale) X.affineCover]
    intro i
    haveI hw : WeaklyEtale (X.affineCover.f i ≫ f) := by
      rw [eq_inf]
      exact ⟨inferInstance,
        MorphismProperty.comp_mem (.diagonal @Flat) _ _
          (inferInstanceAs (Flat (pullback.diagonal (X.affineCover.f i))))
          WeaklyEtale.flat_diagonal⟩
    haveI hfp : LocallyOfFinitePresentation (X.affineCover.f i ≫ f) :=
      MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
    exact this (X.affineCover.f i ≫ f) ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl : Spec.map φ = f⟩ := Spec.homEquiv.symm.surjective f
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at *
  algebraize [φ.hom]
  -- Extract diagonal flatness and convert to lmul' flatness
  have hdiag_flat : Flat (pullback.diagonal (Spec.map φ)) :=
    WeaklyEtale.flat_diagonal
  have hlmul_flat : (Algebra.TensorProduct.lmul' (↑R) (S := ↑S)).toRingHom.Flat := by
    have : Flat (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.lmul' (↑R) (S := ↑S)).toRingHom)) := by
      rw [← MorphismProperty.cancel_right_of_respectsIso @Flat _
        (pullbackSpecIso (↑R) (↑S) (↑S)).inv, ← diagonal_SpecMap (↑R) (↑S)]
      exact hdiag_flat
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp this
  -- Combine into Algebra.WeaklyEtale, which with FinitePresentation gives Etale
  haveI : Algebra.WeaklyEtale (↑R) (↑S) := {
    flat := by
      have : RingHom.Flat φ.hom :=
        (HasRingHomProperty.Spec_iff (P := @Flat)).mp inferInstance
      exact this
    flat_lmul' := hlmul_flat
  }
  -- RingHom.Etale follows from Algebra.Etale
  exact (inferInstance : Algebra.Etale (↑R) (↑S))

end WeaklyEtale

lemma etale_le_weaklyEtale : @Etale ≤ @WeaklyEtale :=
  fun _ _ _ _ ↦ inferInstance

end AlgebraicGeometry
