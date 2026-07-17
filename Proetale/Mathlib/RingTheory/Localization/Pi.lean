/-
Copyright (c) 2026 Christian Merten, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Jingting Wang
-/
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Ring.Pi
import Mathlib.RingTheory.Localization.Defs
import Proetale.Mathlib.Algebra.GroupWithZero.NonZeroDivisors

/-!
# Localization of a product at its non-zero-divisors

A product of localizations at the non-zero-divisors is the localization of the product at its
non-zero-divisors.

## Main results

- `IsLocalization.pi`: if each `L i` is the localization of `V i` at its non-zero-divisors, then
  `Π i, L i` is the localization of `Π i, V i` at its non-zero-divisors.
-/

/-- If each `L i` is the localization of `V i` at its non-zero-divisors, then `Π i, L i` is the
localization of `Π i, V i` at its non-zero-divisors.

The algebra structure on `Π i, L i` over `Π i, V i` is assumed to be componentwise, expressed by
`halg`. -/
theorem IsLocalization.pi {ι : Type*} {V : ι → Type*} {L : ι → Type*}
    [∀ i, CommRing (V i)] [∀ i, CommRing (L i)] [∀ i, Algebra (V i) (L i)]
    [∀ i, IsLocalization (nonZeroDivisors (V i)) (L i)] [Algebra (Π i, V i) (Π i, L i)]
    (halg : ∀ (s : Π i, V i) (i : ι),
      algebraMap (Π i, V i) (Π i, L i) s i = algebraMap (V i) (L i) (s i)) :
    IsLocalization (nonZeroDivisors (Π i, V i)) (Π i, L i) := by
  refine ⟨fun ⟨s, hs⟩ ↦ ?_, fun z ↦ ?_, fun {a b} h ↦ ⟨1, ?_⟩⟩
  · rw [Pi.isUnit_iff]
    intro i
    rw [halg]
    exact IsLocalization.map_units (L i) ⟨s i, Pi.mem_nonZeroDivisors_iff.mp hs i⟩
  · choose p hp using fun i : ι ↦ IsLocalization.surj (nonZeroDivisors (V i)) (z i)
    refine ⟨⟨fun i ↦ (p i).1, ⟨fun i ↦ (p i).2,
      Pi.mem_nonZeroDivisors_iff.mpr fun i ↦ (p i).2.2⟩⟩, funext fun i ↦ ?_⟩
    simp only [Pi.mul_apply, halg]
    exact hp i
  · obtain rfl : a = b := by
      funext i
      refine IsLocalization.injective (S := L i) le_rfl ?_
      have hi := congrFun h i
      rwa [halg, halg] at hi
    rfl
