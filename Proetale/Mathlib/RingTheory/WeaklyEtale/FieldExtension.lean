/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.WeaklyEtale
import Proetale.Algebra.WeakDimension
import Mathlib.RingTheory.PolynomialAlgebra

/-!
# Weakly étale field extensions: basic properties of `L ⊗[K] L`

Let `K → L` be a weakly étale extension of fields. This file collects basic
properties of the tensor product `L ⊗[K] L` and the multiplication map
`μ : L ⊗[K] L → L`, in preparation for the proof of
[Stacks 092P](https://stacks.math.columbia.edu/tag/092P) (a weakly étale extension
of fields is separable algebraic).

## Main results

* `Algebra.WeaklyEtale.surjective_lmul'_of_field` —
  the multiplication map `L ⊗[K] L → L` is surjective.
* `Algebra.WeaklyEtale.absolutelyFlat_tensor_self` —
  `L ⊗[K] L` is absolutely flat (Stacks [092I] applied to the weakly étale
  base change `L → L ⊗[K] L`, with `L` absolutely flat as a field).
* `Algebra.WeaklyEtale.isReduced_tensor_self` —
  `L ⊗[K] L` is reduced.

We also introduce the `L`-algebra evaluation map
`tensorEvalRight : L[X] →ₐ[L] L ⊗[K] L`, `X ↦ 1 ⊗ a`, and check its basic
properties (`X`, `C`, and `X - C a` evaluations, plus that composing with
multiplication recovers `Polynomial.aeval a`).
-/

universe u

open scoped TensorProduct

namespace Algebra.WeaklyEtale

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- The multiplication map `L ⊗[K] L → L` is surjective: `1 ⊗ x ↦ x`. -/
lemma surjective_lmul'_of_field :
    Function.Surjective (Algebra.TensorProduct.lmul' (R := K) (S := L)) := fun x ↦
  ⟨1 ⊗ₜ x, by simp⟩

/-- If `L / K` is weakly étale between fields, then `L ⊗[K] L` is absolutely flat.

This is the special case of Stacks [092I] (weakly étale algebras over absolutely
flat rings are absolutely flat) applied to the base change `L → L ⊗[K] L`: `L` is
absolutely flat as a field, and `L ⊗[K] L` is weakly étale over `L`. -/
instance absolutelyFlat_tensor_self [Algebra.WeaklyEtale K L] :
    Ring.AbsolutelyFlat (L ⊗[K] L) :=
  have : Ring.AbsolutelyFlat L := .of_field L
  Ring.AbsolutelyFlat.of_flat_lmul' L (L ⊗[K] L)
    (Algebra.WeaklyEtale.flat_lmul' L (L ⊗[K] L))

/-- If `L / K` is weakly étale between fields, then `L ⊗[K] L` is reduced.

Derived from `Ring.AbsolutelyFlat (L ⊗[K] L)` via
`Ring.AbsolutelyFlat.isField_of_isLocalization_prime`: it suffices to check that
the localization at every maximal ideal is reduced, and each such localization is
a field. -/
instance isReduced_tensor_self [Algebra.WeaklyEtale K L] :
    IsReduced (L ⊗[K] L) := by
  refine isReduced_ofLocalizationMaximal _ fun P hP ↦ ?_
  have : P.IsPrime := hP.isPrime
  have hfld : IsField (Localization.AtPrime P) :=
    Ring.AbsolutelyFlat.isField_of_isLocalization_prime
      (R := L ⊗[K] L) P (Localization.AtPrime P)
  let _ := hfld.toField
  infer_instance

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
