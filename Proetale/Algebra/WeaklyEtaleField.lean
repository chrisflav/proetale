/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.PolynomialAlgebra
import Proetale.Algebra.IndEtale
import Proetale.Algebra.WeakDimension
import Proetale.Algebra.WeaklyEtale
import Proetale.Mathlib.RingTheory.TensorProduct.Maps

/-!
# Weakly étale algebras over a field

Let `K → L` be a weakly étale extension of fields. This file collects basic
properties of the tensor product `L ⊗[K] L` and the multiplication map
`μ : L ⊗[K] L → L`, in preparation for the proof of
[Stacks 092P](https://stacks.math.columbia.edu/tag/092P) (a weakly étale extension
of fields is separable algebraic).

## Main results

* `Algebra.WeaklyEtale.absolutelyFlat_tensor_self` —
  if `K → L` is weakly étale and `L` is absolutely flat (in particular,
  a field), then `L ⊗[K] L` is absolutely flat. Reducedness follows
  automatically from the general `Ring.AbsolutelyFlat ⇒ IsReduced` instance.

We also introduce the `L`-algebra evaluation map
`tensorEvalRight : L[X] →ₐ[L] L ⊗[K] L`, `X ↦ 1 ⊗ a`, and check its basic
properties (`X`, `C`, and `X - C a` evaluations, plus that composing with
multiplication recovers `Polynomial.aeval a`).
-/

universe u

open scoped TensorProduct

open IntermediateField

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R]

namespace Algebra.WeaklyEtale

/-- If `K → L` is weakly étale and `L` is absolutely flat (e.g. a field), then `L ⊗[K] L`
is absolutely flat.

Special case of Stacks [092I] (weakly étale algebras over absolutely flat rings are absolutely
flat) applied to the base change `L → L ⊗[K] L`. -/
instance absolutelyFlat_tensor_self (K L : Type*) [CommRing K] [CommRing L] [Algebra K L]
    [Ring.AbsolutelyFlat L] [Algebra.WeaklyEtale K L] :
    Ring.AbsolutelyFlat (L ⊗[K] L) :=
  Ring.AbsolutelyFlat.of_flat_lmul' L (L ⊗[K] L)
    (Algebra.WeaklyEtale.flat_lmul' L (L ⊗[K] L))

/-- For any intermediate field `E` of `L/k`, absolute flatness of `L ⊗[k] L` descends to
`E ⊗[k] E`. -/
private lemma absolutelyFlat_tensor_of_intermediateField {L : Type*} [Field L]
    [Algebra k L] (E : IntermediateField k L) [Ring.AbsolutelyFlat (L ⊗[k] L)] :
    Ring.AbsolutelyFlat (E ⊗[k] E) := by
  -- An `E`-linear retraction `π : L → E` of the inclusion induces an additive, unital
  -- retraction `r : L ⊗[k] L → E ⊗[k] E` of `ι : E ⊗[k] E → L ⊗[k] L`, along which von
  -- Neumann regularity of `L ⊗[k] L` descends to `E ⊗[k] E`.
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap E L)
    (LinearMap.ker_eq_bot.mpr (algebraMap E L).injective)
  have hπ' : ∀ c : E, π c = c := fun c ↦ by
    simpa using LinearMap.congr_fun hπ c
  have hπmul : ∀ (c : E) (z : L), π (c * z) = c * π z := by
    intro c z
    have hcz : (c : L) * z = c • z := by rw [Algebra.smul_def, IntermediateField.algebraMap_apply]
    rw [hcz, map_smul, smul_eq_mul]
  let ι : E ⊗[k] E →ₐ[k] L ⊗[k] L := Algebra.TensorProduct.map E.val E.val
  let r : L ⊗[k] L →ₗ[k] E ⊗[k] E :=
    _root_.TensorProduct.map (π.restrictScalars k) (π.restrictScalars k)
  have hr : ∀ (c : E ⊗[k] E) (z : L ⊗[k] L), r (ι c * z) = c * r z := by
    intro c z
    induction c using TensorProduct.induction_on with
    | zero => simp
    | add c c' hc hc' => simp only [map_add, add_mul, hc, hc']
    | tmul c₁ c₂ =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, mul_add, hz, hz']
      | tmul z₁ z₂ =>
        simp only [ι, r, Algebra.TensorProduct.map_tmul, coe_val,
          Algebra.TensorProduct.tmul_mul_tmul, _root_.TensorProduct.map_tmul,
          LinearMap.coe_restrictScalars, hπmul]
  have h1 : r 1 = 1 := by
    have h1L : (1 : L) = ((1 : E) : L) := by simp
    simp only [r, Algebra.TensorProduct.one_def, _root_.TensorProduct.map_tmul,
      LinearMap.coe_restrictScalars]
    rw [h1L, hπ' 1]
  exact .of_forall_exists_eq_mul_self_mul fun b ↦
    Ring.AbsolutelyFlat.exists_eq_mul_self_mul_of_retract ι.toRingHom r.toAddMonoidHom hr h1
      Ring.AbsolutelyFlat.exists_eq_mul_self_mul b

/-- Any weakly étale extension of fields is separable (hence algebraic). -/
lemma isSeparable {L : Type*} [Field L] [Algebra k L] [WeaklyEtale k L] :
    Algebra.IsSeparable k L := by
  refine ⟨fun x ↦ ?_⟩
  -- Absolute flatness of `L ⊗[k] L` descends to `k⟮x⟯ ⊗[k] k⟮x⟯`, hence `k⟮x⟯` is weakly étale
  -- over `k`.
  have hflat : Ring.AbsolutelyFlat (k⟮x⟯ ⊗[k] k⟮x⟯) :=
    absolutelyFlat_tensor_of_intermediateField k⟮x⟯
  have hwe : WeaklyEtale k k⟮x⟯ :=
    ⟨inferInstance, RingHom.Flat.of_pure_ker_of_surjective
      (fun y ↦ ⟨1 ⊗ₜ y, by simp⟩) (Ring.AbsolutelyFlat.flat _)⟩
  -- `k⟮x⟯` is essentially of finite type and formally unramified over `k`, hence separable.
  have hft : Algebra.EssFiniteType k k⟮x⟯ :=
    IntermediateField.essFiniteType_iff.mpr (fg_adjoin_of_finite (Set.toFinite _))
  have hsep : Algebra.IsSeparable k k⟮x⟯ := Algebra.FormallyUnramified.isSeparable k k⟮x⟯
  exact isSeparable_of_mem_isSeparable k L (mem_adjoin_simple_self k x)

/-- Any finitely-generated subalgebra of a weakly étale algebra is étale. -/
lemma etale_of_fg [WeaklyEtale k R] (A : Subalgebra k R) (hA : A.FG) : Etale k A :=
  sorry

variable (k R) in
/-- Any weakly étale algebra over a field is ind-étale. -/
theorem indEtale_field [WeaklyEtale k R] : IndEtale k R :=
  sorry

variable (K L : Type u) [CommRing K] [CommRing L] [Algebra K L]

/-- The `L`-algebra evaluation `L[X] →ₐ[L] L ⊗[K] L` sending `X` to `1 ⊗ a`.
The `L`-algebra structure on `L ⊗[K] L` is the standard `Algebra.TensorProduct`
one, where `c ∈ L` acts as `c ⊗ 1`. Composed with multiplication
`μ : L ⊗[K] L → L` this is `Polynomial.aeval a`. -/
noncomputable def tensorEvalRight (a : L) : Polynomial L →ₐ[L] L ⊗[K] L :=
  Polynomial.aeval (1 ⊗ₜ[K] a)

@[simp]
lemma tensorEvalRight_X (a : L) :
    tensorEvalRight K L a Polynomial.X = (1 ⊗ₜ[K] a : L ⊗[K] L) := by
  simp [tensorEvalRight]

@[simp]
lemma tensorEvalRight_C (a c : L) :
    tensorEvalRight K L a (Polynomial.C c) = (c ⊗ₜ[K] 1 : L ⊗[K] L) := by
  simp [tensorEvalRight, Algebra.TensorProduct.algebraMap_apply]

/-- Composing `tensorEvalRight K L a : L[X] → L ⊗[K] L` with multiplication
`μ : L ⊗[K] L → L` recovers `Polynomial.aeval a`. -/
lemma lmul'_comp_tensorEvalRight (a : L) (p : Polynomial L) :
    Algebra.TensorProduct.lmul' (R := K) (S := L) (tensorEvalRight K L a p) =
      Polynomial.aeval a p := by
  induction p using Polynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n c _ => simp [tensorEvalRight]

/-- `tensorEvalRight K L a` sends `X - C a` to the diagonal `1 ⊗ a - a ⊗ 1`. -/
lemma tensorEvalRight_X_sub_C (a : L) :
    tensorEvalRight K L a (Polynomial.X - Polynomial.C a) =
      (1 ⊗ₜ[K] a - a ⊗ₜ[K] 1 : L ⊗[K] L) := by
  simp

end Algebra.WeaklyEtale
