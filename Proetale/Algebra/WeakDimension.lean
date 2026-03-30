/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.WeaklyEtale
import Mathlib

/-!
# Weak dimension of a commutative ring

Since mathlib does not have `Tor`, we only define some special cases in low dimensions.
-/

/-- A ring `R` is absolutely flat if every ideal of `R` is pure, i.e. `R ⧸ I` is flat. -/
class Ring.AbsolutelyFlat (R : Type*) [CommRing R] where
  flat (I : Ideal R) : Module.Flat R (R ⧸ I)

/-- A ring `R` is of weak dimension `≤ 1` if any finitely generated ideal is flat. -/
class Ring.WeakDimensionLEOne (R : Type*) [CommRing R] where
  flat_of_fg (I : Ideal R) : I.FG → Module.Flat R I

-- Follows from `Ideal.exists_eq_mul_of_pure` in mathlib
lemma exists_eq_mul_of_surjective_flat {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) (x : R) (hx : f x = 0) : ∃ y : R, f y = 1 ∧ y * x = 0 := sorry

lemma exists_eq_mul_of_surjective_flat' {R S ι : Type*} [CommRing R] [CommRing S] [Finite ι]
    (f : R →+* S) (hf : f.Flat) (x : ι → R) (hx : ∀ i, f (x i) = 0) : ∃ y : R, f y = 1 ∧ ∀ i : ι, y * x i = 0 := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e h =>
    obtain ⟨y, hy, hy'⟩ := h (x.comp e) (by grind)
    refine ⟨y, hy, fun i ↦ by simpa using hy' (e.symm i)⟩
  | h_empty => exact ⟨1, by simp, by simp⟩
  | h_option h =>
    obtain ⟨y, hy, hy'⟩ := h (x.comp Option.some) (by grind)
    obtain ⟨z, hz, hz'⟩ := exists_eq_mul_of_surjective_flat f hf (x .none) (by grind)
    refine ⟨y * z, by simp [hy, hz], fun | some i => by grind | none => by grind⟩

namespace Ring.WeakDimensionLEOne

variable (R : Type*) [CommRing R]

/-- If `R` is of weak dimension `≤ 1` if any submodule of a flat module is flat. -/
lemma flat_submodule [Ring.WeakDimensionLEOne R] {M : Type*} [AddCommGroup M] [Module R M]
    (N : Submodule R M) [Module.Flat R M] :
    Module.Flat R N :=
  sorry

end Ring.WeakDimensionLEOne

namespace Ring.AbsolutelyFlat

instance of_field (R : Type*) [Field R] : AbsolutelyFlat R where
  flat _ := inferInstance

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

lemma of_isField (h : IsField R) : AbsolutelyFlat R := @of_field R h.toField

instance [AbsolutelyFlat R] : Module.Flat R M := by
  sorry

variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (h : (Algebra.TensorProduct.lmul' (S := S) R).Flat)

open TensorProduct

include h in
@[stacks 092C]
theorem _root_.Module.Flat.of_flat_lmul'_of_flat [Module.Flat R M] : Module.Flat S M := by
  refine Module.Flat.of_forall_isTrivialRelation fun {l f x} hx ↦ ?_
  obtain ⟨t, ht, ht'⟩ := exists_eq_mul_of_surjective_flat' _ h
    (fun i : Fin l ↦ (1 : S) ⊗ₜ[R] (f i) - (f i) ⊗ₜ[R] (1 : S)) (fun i ↦ by simp)
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
  simp only [AlgHom.toRingHom_eq_coe, map_sum, RingHom.coe_coe,
    Algebra.TensorProduct.lmul'_apply_tmul] at ht
  simp only [Finset.sum_mul, mul_sub, Algebra.TensorProduct.tmul_mul_tmul, sub_eq_zero] at ht'
  let φ (i : Fin l) : S ⊗[R] S →ₗ[R] S ⊗[R] M := LinearMap.lTensor S (LinearMap.toSpanSingleton S M (x i))
  have hg : ∑ y : s ×ˢ Finset.univ, (y.1.1.1 * f y.1.2) ⊗ₜ[R] (y.1.1.2 • x y.1.2) = 0 := by
    simp only [Finset.sum_coe_sort _ (fun y : (S × S) × Fin l ↦ (y.1.1 * f y.2) ⊗ₜ[R] (y.1.2 • x y.2)),
      Finset.sum_product, Finset.sum_comm (s := s)]
    replace ht' := by simpa [φ] using congr(fun i ↦ (φ i) $(ht' i))
    simp only [← ht', Finset.sum_comm (t := s), ← tmul_sum, mul_smul, ← Finset.smul_sum, hx,
      smul_zero, tmul_zero, Finset.sum_const_zero]
  obtain ⟨l', g, y, ha, ha'⟩ := vanishesTrivially_of_sum_tmul_eq_zero_of_rTensor_injective R
    (Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.subtype_injective _)) hg
  refine ⟨l', fun i j ↦ s.attach.sum fun x ↦ x.1.1 * (algebraMap R S) (g ⟨⟨x.1, i⟩, by simp⟩ j),
    y, fun i ↦ ?_, fun j ↦ ?_⟩
  · simp only [Finset.sum_smul, mul_smul, Finset.sum_comm, ← Finset.smul_sum, algebraMap_smul]
    simp only [← ha, ← mul_smul, ← Finset.sum_smul, ← Finset.sum_coe_sort_eq_attach,
      Finset.sum_coe_sort _ fun (i : S × S) ↦ i.1 * i.2, ht, one_smul]
  · simp only [Finset.mul_sum, ← ha' j, ← Finset.sum_product_right']
    exact Finset.sum_bij' (fun a _ ↦ ⟨⟨a.1, a.2⟩, by simp⟩) (fun a _ ↦ ⟨⟨a.1.1, by grind⟩, a.1.2⟩)
      (by simp) (by simp) (by simp) (by simp)
      (by simp_rw [← mul_assoc, mul_comm (f _), mul_comm (_ * _), Algebra.smul_def, forall_true_iff])

include h in
@[stacks 092I "(1)"]
theorem of_flat_lmul' [AbsolutelyFlat R] : AbsolutelyFlat S :=
  ⟨fun _ ↦ Module.Flat.of_flat_lmul'_of_flat R S _ h⟩

end Ring.AbsolutelyFlat
