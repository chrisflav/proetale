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

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R]

namespace Algebra.WeaklyEtale

/-- Any weakly étale extension of fields is algebraic separable -/
lemma isAlgebraic {L : Type*} [Field L] [Algebra k L] [WeaklyEtale k L] : Algebra.IsSeparable k L :=
  sorry

/-- Any finitely-generated subalgebra of a weakly étale algebra is étale. -/
lemma etale_of_fg [WeaklyEtale k R] (A : Subalgebra k R) (hA : A.FG) : Etale k A :=
  sorry

variable (k R) in
/-- Any weakly étale algebra over a field is ind-étale. -/
theorem indEtale_field [WeaklyEtale k R] : IndEtale k R :=
  sorry

/-- If `K → L` is weakly étale and `L` is absolutely flat (e.g. a field), then `L ⊗[K] L`
is absolutely flat.

Special case of Stacks [092I] (weakly étale algebras over absolutely flat rings are absolutely
flat) applied to the base change `L → L ⊗[K] L`. -/
instance absolutelyFlat_tensor_self (K L : Type u) [CommRing K] [CommRing L] [Algebra K L]
    [Ring.AbsolutelyFlat L] [Algebra.WeaklyEtale K L] :
    Ring.AbsolutelyFlat (L ⊗[K] L) :=
  Ring.AbsolutelyFlat.of_flat_lmul' L (L ⊗[K] L)
    (Algebra.WeaklyEtale.flat_lmul' L (L ⊗[K] L))

section Field

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- The multiplication map `L ⊗[K] L → L` is surjective. -/
lemma surjective_lmul'_of_field :
    Function.Surjective (Algebra.TensorProduct.lmul' (R := K) (S := L)) :=
  fun x ↦ ⟨1 ⊗ₜ x, by simp⟩

/-- A weakly étale extension between fields is formally unramified.

Restated for convenience from the general
`Algebra.WeaklyEtale ⇒ Algebra.FormallyUnramified` instance. -/
lemma formallyUnramified_of_isField [Algebra.WeaklyEtale K L] :
    Algebra.FormallyUnramified K L :=
  inferInstance

/-- If `K → L` is a weakly étale extension between fields, then `L ⊗[K] L` is reduced.

Derived from `Ring.AbsolutelyFlat (L ⊗[K] L)` via the local-rings-are-fields
characterisation of absolutely flat rings. -/
instance isReduced_tensor_self [Algebra.WeaklyEtale K L] : IsReduced (L ⊗[K] L) := by
  refine isReduced_ofLocalizationMaximal _ fun P hP ↦ ?_
  have : P.IsPrime := hP.isPrime
  have hfld : IsField (Localization.AtPrime P) :=
    Ring.AbsolutelyFlat.isField_of_isLocalization_prime
      (R := L ⊗[K] L) P (Localization.AtPrime P)
  let _ := hfld.toField
  infer_instance

variable {K L} in
/-- For `a ∈ L`, the element `1 ⊗ a - a ⊗ 1 ∈ L ⊗[K] L` lies in the kernel of
multiplication. -/
lemma sub_mem_ker_lmul' (a : L) :
    (1 ⊗ₜ[K] a - a ⊗ₜ[K] 1 : L ⊗[K] L) ∈
      RingHom.ker (Algebra.TensorProduct.lmul' (R := K) (S := L)).toRingHom := by
  simp [RingHom.mem_ker]

end Field

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
