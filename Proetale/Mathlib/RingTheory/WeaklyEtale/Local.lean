/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.RingHom.Flat

/-!
# Weakly étale is local on the target

We show that being a weakly étale algebra can be checked on a standard cover of the target.

## Main results

- `Algebra.WeaklyEtale.of_span_eq_top_target_of_isLocalizationAway`: weak étaleness can be
  checked on a standard cover of the target.
- `Algebra.WeaklyEtale.of_span_eq_top_target`: `Localization.Away` variant of the above.
-/

universe u v

open TensorProduct

namespace Algebra.WeaklyEtale

/-- Being a weakly étale algebra can be checked on a standard cover of the target. -/
lemma of_span_eq_top_target_of_isLocalizationAway
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} (s : ι → S) (hs : Ideal.span (Set.range s) = ⊤)
    (T : ι → Type*) [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    [∀ i, Algebra S (T i)] [∀ i, IsScalarTower R S (T i)]
    [∀ i, IsLocalization.Away (s i) (T i)]
    [∀ i, Algebra.WeaklyEtale R (T i)] :
    Algebra.WeaklyEtale R S := by
  classical
  let idx : Set.range s → ι := fun r ↦ r.2.choose
  have hidx (r : Set.range s) : s (idx r) = r.1 := r.2.choose_spec
  have hloc : ∀ r : Set.range s, IsLocalization.Away r.1 (T (idx r)) := fun r =>
    hidx r ▸ (inferInstance : IsLocalization.Away (s (idx r)) (T (idx r)))
  refine ⟨?_, ?_⟩
  · exact Module.flat_of_isLocalized_span S S (Set.range s) hs
      (fun r ↦ T (idx r)) (fun r ↦ Algebra.linearMap S (T (idx r)))
      (fun _ ↦ inferInstance)
  · algebraize [(Algebra.TensorProduct.lmul' R (S := S)).toRingHom]
    have : IsScalarTower (S ⊗[R] S) S S := .right
    let alg (r : Set.range s) : Algebra (S ⊗[R] S) (T (idx r)) :=
      ((algebraMap S (T (idx r))).comp (algebraMap (S ⊗[R] S) S)).toAlgebra
    have tower (r : Set.range s) : IsScalarTower (S ⊗[R] S) S (T (idx r)) :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have flat_T (r : Set.range s) : Module.Flat (S ⊗[R] S) (T (idx r)) := by
      let i := idx r
      let α : S →ₐ[R] T i := IsScalarTower.toAlgHom R S (T i)
      have hα : α.toRingHom.Flat :=
        RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (T i) (.powers (s i)))
      have hαα : (Algebra.TensorProduct.map α α).toRingHom.Flat :=
        RingHom.Flat.tensorProductMap hα hα
      have hlmul : (Algebra.TensorProduct.lmul' R (S := T i)).toRingHom.Flat :=
        Algebra.WeaklyEtale.flat_lmul' R (T i)
      have hcomp : ((Algebra.TensorProduct.lmul' R (S := T i)).toRingHom.comp
          (Algebra.TensorProduct.map α α).toRingHom).Flat :=
        RingHom.Flat.comp hαα hlmul
      have hα_eq : α.toRingHom.comp (Algebra.TensorProduct.lmul' R (S := S)).toRingHom =
          (Algebra.TensorProduct.lmul' R (S := T i)).toRingHom.comp
            (Algebra.TensorProduct.map α α).toRingHom := by
        ext x
        all_goals
          simp [Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.map_tmul]
      have heq : algebraMap (S ⊗[R] S) (T i) =
          (Algebra.TensorProduct.lmul' R (S := T i)).toRingHom.comp
            (Algebra.TensorProduct.map α α).toRingHom :=
        hα_eq
      rw [← RingHom.flat_algebraMap_iff, heq]
      exact hcomp
    exact Module.flat_of_isLocalized_span (R := S ⊗[R] S) S S (Set.range s) hs
      (fun r ↦ T (idx r)) (fun r ↦ Algebra.linearMap S (T (idx r))) flat_T

/-- Being a weakly étale algebra can be checked on a standard cover of the target,
applied to the canonical `Localization.Away`. -/
lemma of_span_eq_top_target
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} (s : ι → S) (hs : Ideal.span (Set.range s) = ⊤)
    [∀ i, Algebra.WeaklyEtale R (Localization.Away (s i))] :
    Algebra.WeaklyEtale R S :=
  of_span_eq_top_target_of_isLocalizationAway s hs (fun i ↦ Localization.Away (s i))

end Algebra.WeaklyEtale
