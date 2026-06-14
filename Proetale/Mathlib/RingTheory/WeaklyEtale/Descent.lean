/-
Copyright (c) 2026 The slopetale Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Etale.Weakly
import Proetale.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Faithfully-flat intermediate descent for weakly étale algebras

This file formalises [Stacks 04PV](https://stacks.math.columbia.edu/tag/04PV)
part (2) ("go down"): if `K → B → C` is a tower of commutative ring maps,
`B → C` is faithfully flat, and `K → C` is weakly étale, then `K → B` is
weakly étale.

## Main results

* `Algebra.WeaklyEtale.of_faithfullyFlat_intermediate` —
  if `K → B → C` is a scalar tower, `B → C` is faithfully flat, and
  `K → C` is weakly étale, then `K → B` is weakly étale.
-/

open scoped TensorProduct

namespace Algebra.TensorProduct

variable {R A B : Type*} [CommSemiring R]
  [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra R B]

lemma comp_lmul' (f : A →ₐ[R] B) :
    f.comp (lmul' R (S := A)) = (lmul' R (S := B)).comp (map f f) := by
  ext <;> simp [lmul'_apply_tmul]

end Algebra.TensorProduct

namespace Algebra.WeaklyEtale

/-- [Stacks 04PV](https://stacks.math.columbia.edu/tag/04PV) part (2): if
`K → B → C` is a tower of commutative ring maps with `B → C` faithfully
flat and `K → C` weakly étale, then `K → B` is weakly étale. -/
@[stacks 04PV]
lemma of_faithfullyFlat_intermediate
    {K B C : Type*} [CommRing K] [CommRing B] [CommRing C]
    [Algebra K B] [Algebra K C] [Algebra B C] [IsScalarTower K B C]
    [Module.FaithfullyFlat B C] [Algebra.WeaklyEtale K C] :
    Algebra.WeaklyEtale K B := by
  have hflatB : Module.Flat K B :=
    Module.Flat.of_faithfullyFlat_intermediate (R := K) (B := B) (C := C)
  refine ⟨hflatB, ?_⟩
  set μB : B ⊗[K] B →ₐ[K] B := Algebra.TensorProduct.lmul' (R := K) (S := B)
  set μC : C ⊗[K] C →ₐ[K] C := Algebra.TensorProduct.lmul' (R := K) (S := C)
  set ιBC : B →ₐ[K] C := IsScalarTower.toAlgHom K B C
  set MBC : B ⊗[K] B →ₐ[K] C ⊗[K] C := Algebra.TensorProduct.map ιBC ιBC
  have hcomm : ιBC.comp μB = μC.comp MBC := Algebra.TensorProduct.comp_lmul' ιBC
  have hιBC_flat : ιBC.Flat :=
    (RingHom.flat_algebraMap_iff (R := B) (S := C)).mpr inferInstance
  have hMBC_flat : MBC.Flat := RingHom.Flat.tensorProductMap hιBC_flat hιBC_flat
  have hμC_flat : μC.Flat := Algebra.WeaklyEtale.flat_lmul' K C
  have hcomp_flat : (μC.toRingHom.comp MBC.toRingHom).Flat :=
    RingHom.Flat.comp hMBC_flat hμC_flat
  have h_alg_μB_flat : ((algebraMap B C).comp μB.toRingHom).Flat := by
    have : (algebraMap B C).comp μB.toRingHom = μC.toRingHom.comp MBC.toRingHom :=
      congr_arg AlgHom.toRingHom hcomm
    rw [this]; exact hcomp_flat
  letI : Algebra (B ⊗[K] B) B := μB.toAlgebra
  letI : Algebra (B ⊗[K] B) C := ((algebraMap B C).comp μB.toRingHom).toAlgebra
  have : IsScalarTower (B ⊗[K] B) B C := .of_algebraMap_eq fun _ ↦ rfl
  have : Module.Flat (B ⊗[K] B) C := h_alg_μB_flat
  exact Module.Flat.of_faithfullyFlat_intermediate (R := B ⊗[K] B) (B := B) (C := C)

end Algebra.WeaklyEtale
