/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Extended maximal ideal of a finite extension of a local ring

For a local ring `A` and a finite `A`-algebra `B`, the image
`(IsLocalRing.maximalIdeal A).map (algebraMap A B)` is contained in the Jacobson
radical of `B`. Consequently:

* units modulo `m · B` lift to units in `B`;
* if `A` is Noetherian, the `m·B`-adic intersection
  `⨅ n, (m · B) ^ n` vanishes in `B`.

These are standard consequences of integral going-up
(`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`) and Krull's intersection
theorem (`Ideal.iInf_pow_smul_eq_bot_of_le_jacobson`).
-/

namespace IsLocalRing

variable (A B : Type*) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B]

/-- For a local ring `A` and a finite `A`-algebra `B`, the extended maximal ideal
`m · B` is contained in the Jacobson radical of `B`. -/
theorem map_maximalIdeal_le_jacobson_bot :
    (maximalIdeal A).map (algebraMap A B) ≤ Ideal.jacobson (⊥ : Ideal B) := by
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  rw [Ideal.jacobson_bot, Ring.jacobson_eq_sInf_isMaximal]
  refine le_sInf fun J hJ ↦ ?_
  have hJmax : J.IsMaximal := hJ
  rw [Ideal.map_le_iff_le_comap]
  have hcomap : (J.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal J
  rw [eq_maximalIdeal hcomap]

/-- For a local ring `A` and a finite `A`-algebra `B`, an element of `B` whose image
in `B ⧸ m · B` is a unit is itself a unit in `B`. -/
theorem isUnit_of_isUnit_quotient_mk_map_maximalIdeal {x : B}
    (hx : IsUnit (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)) x)) :
    IsUnit x :=
  have : IsLocalHom (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B))) :=
    isLocalHom_of_le_jacobson_bot _ (map_maximalIdeal_le_jacobson_bot A B)
  IsUnit.of_map (Ideal.Quotient.mk _) _ hx

/-- **Krull's intersection theorem** for the extended maximal ideal of a finite
extension of a Noetherian local ring: `⨅ n, (m · B) ^ n = ⊥` in `B`. -/
theorem iInf_pow_map_maximalIdeal_eq_bot [IsNoetherianRing A] :
    ⨅ n : ℕ, ((maximalIdeal A).map (algebraMap A B)) ^ n = ⊥ := by
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have hjac : (maximalIdeal A).map (algebraMap A B) ≤ Ideal.jacobson (⊥ : Ideal B) :=
    map_maximalIdeal_le_jacobson_bot A B
  convert! Ideal.iInf_pow_smul_eq_bot_of_le_jacobson
    (I := (maximalIdeal A).map (algebraMap A B)) (M := B) hjac with i
  rw [smul_eq_mul, ← Ideal.one_eq_top, mul_one]

end IsLocalRing
