/-
Copyright (c) 2026 The Proetale Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Algebra.Algebra.Pi

/-!
# Localization of a product of fields at a single-coordinate element

This file contains the helper `Localization.Away_pi_field_supportedAt`:
for a product of fields `∀ i, k i`, localizing away from an element `r` whose
support is the singleton `{i₀}` (i.e. `r i₀ ≠ 0` and `r i = 0` for `i ≠ i₀`)
collapses to the single factor `k i₀`.

## Main result

* `Localization.Away_pi_field_supportedAt`: the canonical `S`-algebra
  isomorphism `Localization.Away r ≃ₐ[S] k i₀` for `r` supported at `i₀`.
-/

namespace Localization

variable {S : Type*} [CommRing S]
variable {I : Type*}
variable (k : I → Type*) [∀ i, Field (k i)] [∀ i, Algebra S (k i)]

/-- For a family of fields `k i` (each an `S`-algebra) and an element
`r : ∀ i, k i` supported only at the index `i₀` (so `r i₀ ≠ 0` and `r i = 0`
for `i ≠ i₀`), the localization `(∀ i, k i)[r⁻¹]` is `S`-algebra isomorphic
to the single factor `k i₀`. -/
theorem Away_pi_field_supportedAt
    (i₀ : I) (r : ∀ i, k i) (hr_i₀ : r i₀ ≠ 0)
    (hr_other : ∀ i, i ≠ i₀ → r i = 0) :
    Nonempty (Localization.Away r ≃ₐ[S] k i₀) := by
  classical
  -- The `i₀`-projection as an `S`-algebra hom.
  let π : (∀ i, k i) →ₐ[S] k i₀ := Pi.evalAlgHom S k i₀
  -- `π r = r i₀` is a nonzero element of the field `k i₀`, hence a unit.
  have hunit_πr : IsUnit (π r) := by
    rw [show π r = r i₀ from Pi.evalAlgHom_apply S k i₀ r]
    exact hr_i₀.isUnit
  -- Extend `π` to `extn : Localization.Away r →ₐ[S] k i₀`.
  have hunit_all : ∀ y : Submonoid.powers r, IsUnit (π (y : ∀ i, k i)) := by
    rintro ⟨_, n, rfl⟩
    exact map_pow π r n ▸ hunit_πr.pow n
  let extn : Localization.Away r →ₐ[S] k i₀ :=
    IsLocalization.liftAlgHom (M := Submonoid.powers r) hunit_all
  have hextn_algebraMap (x : ∀ i, k i) :
      extn (algebraMap (∀ i, k i) (Localization.Away r) x) = π x := by
    simp [extn, IsLocalization.lift_eq]
  -- `π` is surjective via `Pi.single i₀`; hence so is `extn`.
  have hπ_surj : Function.Surjective π := fun y ↦
    ⟨Pi.single i₀ y, by simp [π, Pi.evalAlgHom_apply, Pi.single_eq_same]⟩
  have hlift_surj : Function.Surjective extn := fun y ↦ by
    obtain ⟨x, hx⟩ := hπ_surj y
    exact ⟨algebraMap _ _ x, (hextn_algebraMap x).trans hx⟩
  -- Injectivity: if `extn q = 0`, write `q = mk' x ⟨rⁿ, _⟩`; then `π x = x i₀ = 0`,
  -- so `r * x = 0` componentwise, hence `q = 0` by `IsLocalization.mk'_eq_zero_iff`.
  have hlift_inj : Function.Injective extn := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨⟨x, s⟩, hxs⟩ :=
      IsLocalization.mk'_surjective (M := Submonoid.powers r) (S := Localization.Away r) q
    rw [← hxs] at hq ⊢
    -- Clear the denominator: `extn (mk' x s) * extn (alg s) = π x`.
    have hmul : extn (IsLocalization.mk' (Localization.Away r) x s) *
        extn (algebraMap (∀ i, k i) (Localization.Away r) (s : ∀ i, k i)) = π x := by
      rw [← map_mul, IsLocalization.mk'_spec, hextn_algebraMap]
    rw [hextn_algebraMap, hq, zero_mul] at hmul
    -- `π x = x i₀ = 0`.
    have hx_i₀ : x i₀ = 0 := (Pi.evalAlgHom_apply S k i₀ x).symm.trans hmul.symm
    -- Componentwise, `r * x = 0`.
    have hrx_zero : r * x = 0 := by
      funext i
      by_cases h : i = i₀
      · change r i * x i = 0
        rw [h, hx_i₀, mul_zero]
      · change r i * x i = 0
        rw [hr_other i h, zero_mul]
    rw [IsLocalization.mk'_eq_zero_iff]
    exact ⟨⟨r, Submonoid.mem_powers r⟩, hrx_zero⟩
  exact ⟨AlgEquiv.ofBijective extn ⟨hlift_inj, hlift_surj⟩⟩

end Localization
