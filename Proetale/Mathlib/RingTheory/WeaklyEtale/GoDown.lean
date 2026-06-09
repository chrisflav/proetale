/-
Copyright (c) 2026 The slopetale Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Faithfully-flat intermediate descent for weakly étale algebras

This file formalises [Stacks 04PV](https://stacks.math.columbia.edu/tag/04PV)
part (2) ("go down"): if `K → B → C` is a tower of commutative ring maps,
`B → C` is faithfully flat, and `K → C` is weakly étale, then `K → B` is
weakly étale.

## Main result

* `Algebra.WeaklyEtale.of_faithfullyFlat_intermediate` —
  if `K → B → C` is a scalar tower, `B → C` is faithfully flat, and
  `K → C` is weakly étale, then `K → B` is weakly étale.

## Helper

* `Module.Flat.of_faithfullyFlat_intermediate` — flatness descent along a
  faithfully flat intermediate algebra in a tower.
-/

universe u

open scoped TensorProduct
open Algebra

namespace Module.Flat

variable (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]

/-- **Faithfully-flat intermediate descent of flatness in a tower.**

If `R → B → C` is a tower of commutative ring maps with `B → C` faithfully
flat and `C` flat over `R`, then `B` is flat over `R`.

This is the module-level core of
[Stacks `algebra-lemma-flatness-descends-more-general`](https://stacks.math.columbia.edu/tag/03C4)
specialised to `M = B`, `M' = C ⊗_B B = C`. -/
lemma of_faithfullyFlat_intermediate
    [Module.FaithfullyFlat B C] [Module.Flat R C] :
    Module.Flat R B := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  -- Bundle `f.lTensor B` as a `B`-linear map.
  let fB : B ⊗[R] N →ₗ[B] B ⊗[R] P := TensorProduct.AlgebraTensorModule.lTensor B B f
  -- It suffices to show `fB` is injective as a function.
  change Function.Injective (fB : B ⊗[R] N → B ⊗[R] P)
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective B C fB]
  -- Goal: `Function.Injective (fB.lTensor C : C ⊗[B] (B ⊗[R] N) → C ⊗[B] (B ⊗[R] P))`.
  let cN : C ⊗[B] (B ⊗[R] N) ≃ₗ[C] C ⊗[R] N :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R B C C N
  let cP : C ⊗[B] (B ⊗[R] P) ≃ₗ[C] C ⊗[R] P :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R B C C P
  have key : ∀ x : C ⊗[B] (B ⊗[R] N),
      (fB.lTensor C) x = cP.symm (LinearMap.lTensor C f (cN x)) := by
    intro x
    induction x with
    | zero => simp
    | tmul c bn =>
      induction bn with
      | zero => simp
      | tmul b n =>
        simp only [LinearMap.lTensor_tmul, fB,
          TensorProduct.AlgebraTensorModule.lTensor_tmul, cN, cP,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
        rw [show (b ⊗ₜ[R] f n : B ⊗[R] P) = b • (1 ⊗ₜ[R] f n) from by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
        rw [← TensorProduct.smul_tmul]
      | add x y hx hy =>
        simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | add x y hx hy => simp [hx, hy]
  have hC_inj : Function.Injective (LinearMap.lTensor C f) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  intro x y hxy
  apply cN.injective
  apply hC_inj
  apply cP.symm.injective
  rw [← key x, ← key y, hxy]

end Module.Flat

namespace Algebra.WeaklyEtale

/-- **Stacks [04PV] part (2) — "go down" for weakly étale algebras.**

If `K → B → C` is a tower of commutative ring maps with `B → C` faithfully
flat and `K → C` weakly étale, then `K → B` is weakly étale.

This is the structural cycle-breaker for proofs that descend weakly-étale
structure from a faithfully flat extension. -/
lemma of_faithfullyFlat_intermediate
    {K B C : Type u} [CommRing K] [CommRing B] [CommRing C]
    [Algebra K B] [Algebra K C] [Algebra B C] [IsScalarTower K B C]
    [Module.FaithfullyFlat B C] [Algebra.WeaklyEtale K C] :
    Algebra.WeaklyEtale K B := by
  -- Part 1: Flatness of `K → B`.
  have hflatB : Module.Flat K B :=
    Module.Flat.of_faithfullyFlat_intermediate K B C
  refine ⟨hflatB, ?_⟩
  -- Part 2: `(lmul' K : B ⊗_K B → B).Flat`.
  -- We package this as `RingHom.Flat` and reduce to module-flat at the end.
  set μB : B ⊗[K] B →ₐ[K] B := Algebra.TensorProduct.lmul' (R := K) (S := B) with hμB_def
  set μC : C ⊗[K] C →ₐ[K] C := Algebra.TensorProduct.lmul' (R := K) (S := C) with hμC_def
  set ιBC : B →ₐ[K] C := IsScalarTower.toAlgHom K B C with hιBC_def
  set MBC : B ⊗[K] B →ₐ[K] C ⊗[K] C := Algebra.TensorProduct.map ιBC ιBC with hMBC_def
  -- The commutative square: `ιBC ∘ μB = μC ∘ MBC` as ring homs.
  have hcomm : (algebraMap B C).comp μB.toRingHom = μC.toRingHom.comp MBC.toRingHom := by
    refine RingHom.ext fun x => ?_
    induction x with
    | zero => simp
    | tmul b₁ b₂ =>
      simp [μB, μC, MBC, ιBC, Algebra.TensorProduct.lmul'_apply_tmul,
        Algebra.TensorProduct.map_tmul, IsScalarTower.toAlgHom_apply]
    | add x y hx hy =>
      simp only [map_add, RingHom.comp_apply] at hx hy ⊢
      rw [hx, hy]
  -- `ιBC` is flat as a `K`-algebra map.
  have hιBC_flat : ιBC.Flat := by
    show ιBC.toRingHom.Flat
    have : ιBC.toRingHom = algebraMap B C := rfl
    rw [this, RingHom.flat_algebraMap_iff]
    infer_instance
  -- `MBC.Flat` from `RingHom.Flat.tensorProductMap`.
  have hMBC_flat : MBC.Flat := RingHom.Flat.tensorProductMap hιBC_flat hιBC_flat
  -- `μC.Flat` from `WeaklyEtale K C`.
  have hμC_flat : μC.Flat := Algebra.WeaklyEtale.flat_lmul' K C
  -- Composition `(μC.comp MBC).Flat`.
  have hcomp_flat : (μC.toRingHom.comp MBC.toRingHom).Flat :=
    RingHom.Flat.comp hMBC_flat hμC_flat
  -- Via the commutative square, the same composite equals `(algebraMap B C).comp μB`.
  have h_alg_μB_flat : ((algebraMap B C).comp μB.toRingHom).Flat := hcomm ▸ hcomp_flat
  -- Now reduce to module-flat. Set up the algebra `(B ⊗_K B)-algebra` structures on
  -- `B` and `C` consistent with the maps above.
  letI algBB_B : Algebra (B ⊗[K] B) B := μB.toAlgebra
  letI algBB_C : Algebra (B ⊗[K] B) C := ((algebraMap B C).comp μB.toRingHom).toAlgebra
  haveI tower_BB_B_C : IsScalarTower (B ⊗[K] B) B C := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rfl
  -- `Module.Flat (B ⊗_K B) C` from `((algebraMap B C).comp μB).Flat`.
  haveI hflat_BB_C : Module.Flat (B ⊗[K] B) C := h_alg_μB_flat
  -- Descend to `Module.Flat (B ⊗_K B) B`.
  have hflat_BB_B : Module.Flat (B ⊗[K] B) B :=
    Module.Flat.of_faithfullyFlat_intermediate (B ⊗[K] B) B C
  -- Conclude `(lmul' K (S := B)).Flat = μB.Flat`.
  change μB.Flat
  exact hflat_BB_B

end Algebra.WeaklyEtale
