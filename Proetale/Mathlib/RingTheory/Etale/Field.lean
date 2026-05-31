/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Etale.Field
import Proetale.Mathlib.Algebra.Algebra.Pi

/-!
# Algebra homomorphisms from an étale algebra to a local ring

The main result is `IsSeparable.of_algHom_etale_to_isLocalRing`: every element of the image
of an algebra hom from an étale algebra over a field to a local ring is separable.
-/

universe u

/-- If `A` is an étale algebra over a field `k` and `φ : A →ₐ[k] B` is an algebra homomorphism
to a local ring `B`, then every element of the image of `φ` is separable over `k`. -/
lemma IsSeparable.of_algHom_etale_to_isLocalRing (k : Type u) [Field k] (A : Type u)
    [CommRing A] [Algebra k A] [Algebra.Etale k A] (B : Type u) [CommRing B] [Algebra k B]
    [IsLocalRing B] (φ : A →ₐ[k] B) (a : A) : IsSeparable k (φ a) := by
  nontriviality B
  have : Module.Finite k A := Algebra.FormallyUnramified.finite_of_free k A
  obtain ⟨I, _, Ai, hfield, halg, e, hprop⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (K := k) (A := A)).mp inferInstance
  letI : ∀ i, Field (Ai i) := hfield
  letI : ∀ i, Algebra k (Ai i) := halg
  classical
  let ψ : (∀ i, Ai i) →ₐ[k] B := φ.comp e.symm
  obtain ⟨j, hj, hothers⟩ := ψ.exists_pi_single_eq_one_of_isLocalRing
  let τ := ψ.piFactor j hj hothers
  have hφa : φ a = τ (e a j) := by
    rw [← ψ.eq_piFactor_apply j hj hothers (e a)]
    exact (congrArg φ (e.symm_apply_apply a)).symm
  rw [hφa]
  have : Algebra.IsSeparable k (Ai j) := (hprop j).2
  have hb_sep : IsSeparable k (e a j) := Algebra.IsSeparable.isSeparable k _
  refine hb_sep.of_dvd <| minpoly.dvd k _ ?_
  rw [Polynomial.aeval_algHom_apply]
  simp [minpoly.aeval]
