/-
Copyright (c) 2026 The Proetale Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Localization.Away.Basic
import Proetale.Mathlib.Algebra.Algebra.Pi

/-!
# Localization of a product ring at a single-coordinate element

For a family of commutative rings `k i` (each an `S`-algebra) and an element `Pi.single i₀ s`
supported only at the index `i₀`, the localization `(∀ i, k i)[1/(Pi.single i₀ s)]` is
`S`-algebra isomorphic to `(k i₀)[1/s]`.

## Main result

* `Localization.awayPiSingleEquiv`: the canonical `S`-algebra isomorphism
  `Localization.Away (Pi.single i₀ s) ≃ₐ[S] Localization.Away s`.
-/

namespace Localization

variable {S : Type*} [CommRing S]
variable {I : Type*} [DecidableEq I]
variable (k : I → Type*) [∀ i, CommRing (k i)] [∀ i, Algebra S (k i)]

/-- For a family of commutative `S`-algebras `k i` and `s : k i₀`, localizing the product
`∀ i, k i` at the singleton-supported element `Pi.single i₀ s` collapses to localizing the
`i₀`-factor at `s`. -/
noncomputable def awayPiSingleEquiv (i₀ : I) (s : k i₀) :
    Localization.Away (Pi.single i₀ s) ≃ₐ[S] Localization.Away s := by
  set r : ∀ i, k i := Pi.single i₀ s with hr_def
  let f : (∀ i, k i) →ₐ[S] Localization.Away s :=
    (IsScalarTower.toAlgHom S (k i₀) (Localization.Away s)).comp (Pi.evalAlgHom S k i₀)
  have hf_apply (x : ∀ i, k i) : f x = algebraMap (k i₀) (Localization.Away s) (x i₀) := rfl
  have hf_r : f r = algebraMap (k i₀) (Localization.Away s) s := by simp [hf_apply, r]
  have hf_powers : ∀ y : Submonoid.powers r, IsUnit (f y) := by
    rintro ⟨_, n, rfl⟩
    rw [map_pow, hf_r]
    exact (IsLocalization.Away.algebraMap_isUnit s).pow n
  let extn : Localization.Away r →ₐ[S] Localization.Away s :=
    IsLocalization.liftAlgHom (M := Submonoid.powers r) hf_powers
  have hextn_alg (x : ∀ i, k i) :
      extn (algebraMap (∀ i, k i) (Localization.Away r) x) = f x :=
    IsLocalization.lift_eq _ x
  refine AlgEquiv.ofBijective extn ⟨?_, ?_⟩
  · -- Injectivity.
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨⟨x, t⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (M := Submonoid.powers r) (S := Localization.Away r) q
    have hfx : f x = 0 := by
      have hmul : extn (IsLocalization.mk' (Localization.Away r) x t) *
          extn (algebraMap (∀ i, k i) (Localization.Away r) t) = f x := by
        rw [← map_mul, IsLocalization.mk'_spec, hextn_alg]
      rw [hq, zero_mul] at hmul
      exact hmul.symm
    -- `f x = algebraMap (k i₀) _ (x i₀) = 0` produces some `s^m` killing `x i₀`.
    rw [hf_apply] at hfx
    obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers s) _ _).mp hfx
    -- `r ^ (m + 1) * x = 0` componentwise, so `mk' x t = 0`.
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨r ^ (m + 1), m + 1, rfl⟩, ?_⟩
    show r ^ (m + 1) * x = 0
    funext j
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply]
    by_cases hj : j = i₀
    · subst hj
      rw [hr_def, Pi.single_eq_same, pow_succ, mul_right_comm, hm, zero_mul]
    · rw [hr_def, Pi.single_eq_of_ne hj, zero_pow m.succ_ne_zero, zero_mul]
  · -- Surjectivity: `mk' x sⁿ` lifts via `mk' (Pi.single i₀ x) rⁿ`.
    intro y
    obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (M := Submonoid.powers s) (S := Localization.Away s) y
    let t : Submonoid.powers r := ⟨r ^ n, n, rfl⟩
    refine ⟨IsLocalization.mk' (Localization.Away r) (Pi.single i₀ x : ∀ i, k i) t, ?_⟩
    change IsLocalization.lift hf_powers
        (IsLocalization.mk' (Localization.Away r) (Pi.single i₀ x) t) = _
    rw [IsLocalization.lift_mk'_spec]
    show f (Pi.single i₀ x) = f (r ^ n) * _
    rw [hf_apply, Pi.evalAlgHom_apply, Pi.single_eq_same, map_pow, hf_r, ← map_pow]
    exact (IsLocalization.mk'_spec _ x ⟨s ^ n, n, rfl⟩).symm

end Localization
