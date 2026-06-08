/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalRing.Basic

/-!
# Idempotents in local rings and in the Jacobson radical

In a local ring, the only idempotent elements are `0` and `1`.
More generally, any idempotent lying in the Jacobson radical of an arbitrary
commutative ring must be zero.
-/

/-- An idempotent that lies in the Jacobson radical is zero.

If `e` is idempotent and `e ∈ jacobson ⊥`, then `1 - e` is a unit (by definition of
the Jacobson radical applied to `-1`). Combined with the idempotent relation
`e * (1 - e) = 0`, multiplying by `(1 - e)⁻¹` gives `e = 0`. -/
lemma IsIdempotentElem.eq_zero_of_mem_jacobson_bot {R : Type*} [CommRing R]
    {e : R} (he : IsIdempotentElem e) (hmem : e ∈ Ideal.jacobson (⊥ : Ideal R)) :
    e = 0 := by
  rw [Ideal.mem_jacobson_bot] at hmem
  have hu : IsUnit (1 - e) := by
    have := hmem (-1)
    rwa [mul_neg_one, neg_add_eq_sub] at this
  exact hu.mul_left_eq_zero.mp he.mul_one_sub_self

/-- In a local ring, every idempotent element is `0` or `1`. -/
lemma IsIdempotentElem.eq_zero_or_one_of_isLocalRing {R : Type*} [CommRing R]
    [IsLocalRing R] {e : R} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hsum : e + (1 - e) = 1 := by ring
  have hmul : e * (1 - e) = 0 := he.mul_one_sub_self
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hsum with hu | hu
  · exact .inr (sub_eq_zero.mp (hu.mul_right_eq_zero.mp hmul)).symm
  · exact .inl (hu.mul_left_eq_zero.mp hmul)
