/-
Copyright (c) 2026 Christian Merten, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Jingting Wang
-/
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# The image of an integrally closed subring

If `A` is integrally closed in `L` and `A → L` is injective, then the image of `A` in `L`
is integrally closed in `L`.

## Main results

- `IsIntegrallyClosedIn.algebraMap_range`: the range of `algebraMap A L` is integrally closed
  in `L`, when `A` is integrally closed in `L` and `A → L` is injective.
-/

/-- If `A` is integrally closed in `L` and `algebraMap A L` is injective, then the range of
`algebraMap A L` is integrally closed in `L`. -/
theorem IsIntegrallyClosedIn.algebraMap_range {A L : Type*} [CommRing A] [CommRing L]
    [Algebra A L] [FaithfulSMul A L] [IsIntegrallyClosedIn A L] :
    IsIntegrallyClosedIn (algebraMap A L).range L := by
  rw [Subring.isIntegrallyClosedIn_iff]
  intro x hx
  obtain ⟨p, hp, hpe⟩ := hx
  let e : A ≃+* (algebraMap A L).range :=
    RingEquiv.ofBijective (algebraMap A L).rangeRestrict
      ⟨fun a b h ↦ FaithfulSMul.algebraMap_injective A L (congrArg Subtype.val h),
        (algebraMap A L).rangeRestrict_surjective⟩
  have ha : IsIntegral A x := by
    refine ⟨p.map e.symm.toRingHom, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap A L).comp e.symm.toRingHom =
        algebraMap (algebraMap A L).range L := by
      ext y
      exact congrArg Subtype.val (e.apply_symm_apply y)
    rw [hcomp]
    exact hpe
  exact IsIntegrallyClosedIn.isIntegral_iff.mp ha
