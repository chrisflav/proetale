/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Idempotents in local rings and in the Jacobson radical

In a local ring, the only idempotent elements are `0` and `1`.
More generally, any idempotent lying in the Jacobson radical of an arbitrary
commutative ring must be zero.
-/

/-- An idempotent element of a commutative ring that lies in the Jacobson radical
(of the zero ideal) is zero. -/
lemma IsIdempotentElem.eq_zero_of_mem_jacobson_bot {R : Type*} [CommRing R]
    {e : R} (he : IsIdempotentElem e) (hmem : e ∈ Ideal.jacobson (⊥ : Ideal R)) :
    e = 0 := by
  rw [Ideal.mem_jacobson_bot] at hmem
  have hu : IsUnit (1 - e) := by simpa [mul_neg_one, neg_add_eq_sub] using hmem (-1)
  exact hu.mul_left_eq_zero.mp he.mul_one_sub_self

/-- In a local ring, every idempotent element is `0` or `1`. -/
lemma IsIdempotentElem.eq_zero_or_one_of_isLocalRing {R : Type*} [CommRing R]
    [IsLocalRing R] {e : R} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases Classical.em (e ∈ IsLocalRing.maximalIdeal R) with hmem | hnmem
  · exact .inl <| he.eq_zero_of_mem_jacobson_bot <| by
      rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  · rw [IsLocalRing.notMem_maximalIdeal] at hnmem
    exact .inr (sub_eq_zero.mp (hnmem.mul_right_eq_zero.mp he.mul_one_sub_self)).symm
