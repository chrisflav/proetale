/-
Copyright (c) 2026 Christian Merten, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Jingting Wang
-/
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.GroupWithZero.Pi
import Mathlib.Algebra.Notation.Pi.Basic

/-!
# Non-zero-divisors of a product

We characterize the non-zero-divisors of a product of monoids with zero componentwise.

## Main results

- `Pi.mem_nonZeroDivisors_iff`: an element of a product `Π i, R i` is a non-zero-divisor if and
  only if each of its components is a non-zero-divisor.
-/

/-- An element of a product `Π i, R i` is a non-zero-divisor if and only if each of its
components is a non-zero-divisor. -/
theorem Pi.mem_nonZeroDivisors_iff {ι : Type*} {R : ι → Type*} [∀ i, MonoidWithZero (R i)]
    {s : Π i, R i} :
    s ∈ nonZeroDivisors (Π i, R i) ↔ ∀ i, s i ∈ nonZeroDivisors (R i) := by
  classical
  simp only [_root_.mem_nonZeroDivisors_iff]
  constructor
  · rintro ⟨hl, hr⟩ i
    refine ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩
    · have hs : s * Pi.single i z = 0 := by
        funext j
        rcases eq_or_ne j i with rfl | hj
        · simpa using hz
        · simp [Pi.single_eq_of_ne hj]
      simpa using congrFun (hl _ hs) i
    · have hs : Pi.single i z * s = 0 := by
        funext j
        rcases eq_or_ne j i with rfl | hj
        · simpa using hz
        · simp [Pi.single_eq_of_ne hj]
      simpa using congrFun (hr _ hs) i
  · intro h
    refine ⟨fun t ht ↦ funext fun i ↦ (h i).1 (t i) (congrFun ht i),
      fun t ht ↦ funext fun i ↦ (h i).2 (t i) (congrFun ht i)⟩
