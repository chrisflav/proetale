/-
Copyright (c) 2026 The slopetale Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

open TensorProduct

lemma Module.FaithfullyFlat.of_nontrivial_tensor_quotient
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Flat R M] (H : ∀ (m : Ideal R), m.IsMaximal → Nontrivial ((R ⧸ m) ⊗[R] M)) :
    Module.FaithfullyFlat R M where
  submodule_ne_top m hm := by
    rw [ne_eq, ← Submodule.Quotient.subsingleton_iff, not_subsingleton_iff_nontrivial,
      (TensorProduct.quotTensorEquivQuotSMul M m).symm.nontrivial_congr]
    exact H m hm

namespace Module.Flat

/-- If `R → B → C` is a tower of commutative ring maps with `B → C` faithfully
flat and `C` flat over `R`, then `B` is flat over `R`.

This is a special case (`M = B`) of [Stacks 03C4](https://stacks.math.columbia.edu/tag/03C4). -/
@[stacks 03C4]
lemma of_faithfullyFlat_intermediate
    {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
    [Module.FaithfullyFlat B C] [Module.Flat R C] :
    Module.Flat R B := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  let fB : B ⊗[R] N →ₗ[B] B ⊗[R] P := AlgebraTensorModule.lTensor B B f
  rw [show (f.lTensor B : B ⊗[R] N → B ⊗[R] P) = fB from rfl,
    ← FaithfullyFlat.lTensor_injective_iff_injective B C fB]
  let cN : C ⊗[B] (B ⊗[R] N) ≃ₗ[C] C ⊗[R] N :=
    AlgebraTensorModule.cancelBaseChange R B C C N
  let cP : C ⊗[B] (B ⊗[R] P) ≃ₗ[C] C ⊗[R] P :=
    AlgebraTensorModule.cancelBaseChange R B C C P
  have hkey : ∀ x : C ⊗[B] (B ⊗[R] N),
      fB.lTensor C x = cP.symm (LinearMap.lTensor C f (cN x)) := by
    intro x
    induction x with
    | zero => simp
    | tmul c bn =>
      induction bn with
      | zero => simp
      | tmul b n =>
        simp only [LinearMap.lTensor_tmul, fB,
          AlgebraTensorModule.lTensor_tmul, cN, cP,
          AlgebraTensorModule.cancelBaseChange_tmul,
          AlgebraTensorModule.cancelBaseChange_symm_tmul]
        have heq : (b ⊗ₜ[R] f n : B ⊗[R] P) = b • (1 ⊗ₜ[R] f n) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [heq, ← TensorProduct.smul_tmul]
      | add x y hx hy =>
        simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | add x y hx hy => simp [hx, hy]
  have hC : Function.Injective (LinearMap.lTensor C f) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  intro x y hxy
  exact cN.injective (hC (cP.symm.injective (by rw [← hkey, ← hkey, hxy])))

end Module.Flat
