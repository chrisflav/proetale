/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.LocalRing.Basic

/-!
# Idempotents in local rings
-/

/-- In a local ring, every idempotent element is `0` or `1`. -/
lemma IsIdempotentElem.eq_zero_or_one_of_isLocalRing {R : Type*} [CommRing R]
    [IsLocalRing R] {e : R} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hsum : e + (1 - e) = 1 := by ring
  have hmul : e * (1 - e) = 0 := by
    have : e * (1 - e) = e - e * e := by ring
    rw [this, he.eq, sub_self]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hsum with hu | hu
  · exact .inr (sub_eq_zero.mp (hu.mul_right_eq_zero.mp hmul)).symm
  · refine .inl (hu.mul_right_eq_zero.mp ?_)
    rwa [mul_comm]
