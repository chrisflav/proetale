import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.TensorProduct.Maps

open TensorProduct

namespace Algebra

lemma TensorProduct.lmul'_surjective {R S : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] :
    Function.Surjective (Algebra.TensorProduct.lmul' (R := R) (S := S)) :=
  fun x ↦ ⟨1 ⊗ₜ x, by simp⟩

lemma TensorProduct.one_tmul_sub_tmul_one_mem_ker_lmul' {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (a : S) :
    (1 ⊗ₜ[R] a - a ⊗ₜ[R] 1 : S ⊗[R] S) ∈
      RingHom.ker (Algebra.TensorProduct.lmul' (R := R) (S := S)).toRingHom := by
  simp [RingHom.mem_ker]

section

variable (R S T A C D : Type*) [CommRing R] [CommRing S] [CommRing T]
    [CommRing A] [CommRing C] [CommRing D] [Algebra R S] [Algebra R T] [Algebra S T]
    [Algebra R A] [Algebra R C] [Algebra R D]
    [Algebra S A] [IsScalarTower R S A] [Algebra S C] [IsScalarTower R S C]
    [Algebra T A] [IsScalarTower R T A] [IsScalarTower S T A]

def TensorProduct.assoc' :
    (A ⊗[S] C) ⊗[R] D ≃ₐ[T] A ⊗[S] (C ⊗[R] D) :=
  AlgEquiv.ofLinearEquiv
    (AlgebraTensorModule.assoc R S T A C D)
    (by simp [Algebra.TensorProduct.one_def])
    ((LinearMap.map_mul_iff _).mpr <| by ext; simp)

@[simp] theorem TensorProduct.assoc'_toLinearEquiv :
    (TensorProduct.assoc' R S T A C D).toLinearEquiv =
  AlgebraTensorModule.assoc R S T A C D := rfl

@[simp]
theorem TensorProduct.assoc'_tmul (a : A) (b : C) (c : D) :
    TensorProduct.assoc' R S T A C D ((a ⊗ₜ b) ⊗ₜ c) = a ⊗ₜ (b ⊗ₜ c) := rfl

@[simp]
theorem TensorProduct.assoc'_symm_tmul (a : A) (b : C) (c : D) :
    (TensorProduct.assoc' R S T A C D).symm (a ⊗ₜ (b ⊗ₜ c)) = (a ⊗ₜ b) ⊗ₜ c := rfl

end

end Algebra
