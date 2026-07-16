/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Proetale.Mathlib.RingTheory.Henselian
import Proetale.Mathlib.RingTheory.Etale.Henselian

/-!
# Local rings and integral algebras

This file collects miscellaneous lemmas relating local rings, integral ring
homomorphisms, and Henselian local rings.  These are used in the proof of
[Stacks 097Z](https://stacks.math.columbia.edu/tag/097Z) (over a strictly
Henselian local ring, a weakly étale local algebra is the ring itself).

## Main statements

* `HenselianLocalRing.exists_pi_of_finite` ([Stacks 04GH (1)]
  (https://stacks.math.columbia.edu/tag/04GH)):
  A finite algebra over a Henselian local ring decomposes as a finite product
  of Henselian local rings, each finite over the base.
* `IsLocalRing.of_henselianLocalRing_of_isIntegral_of_isDomain`:
  An integral algebra over a Henselian local ring that is an integral domain is local.
* `Algebra.IsAlgebraic.residueField_of_isIntegral`:
  The residue field extension induced by a local integral homomorphism of local rings
  is algebraic.
* `Algebra.IsLocalRing.tensorProduct_of_isPurelyInseparable_residueField`
  ([Stacks 092Y](https://stacks.math.columbia.edu/tag/092Y)):
  If `R → S` is local and integral and either `κ(S)/κ(R)` or `κ(T)/κ(R)` is purely
  inseparable, the tensor product `S ⊗[R] T` is a local ring.
-/

universe u

open TensorProduct

namespace HenselianLocalRing

section PiOfFinite

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
variable (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S]

/-- A finite algebra over a Henselian local ring is, as a ring, a finite product of
Henselian local rings, each finite over the base.

[Stacks 04GH (1)](https://stacks.math.columbia.edu/tag/04GH).

This is destined to go directly to Mathlib, so it should not be worked on here. -/
theorem exists_pi_of_finite :
    ∃ (ι : Type u) (_ : Fintype ι) (B : ι → Type u) (_ : ∀ i, CommRing (B i))
      (_ : ∀ i, IsLocalRing (B i)) (_ : ∀ i, HenselianLocalRing (B i))
      (_ : ∀ i, Algebra R (B i)) (_ : ∀ i, Module.Finite R (B i)),
        Nonempty (S ≃ₐ[R] (Π i, B i)) :=
  sorry

end PiOfFinite

end HenselianLocalRing

namespace IsLocalRing

open Polynomial

/-- An integral algebra over a Henselian local ring that is an integral domain is local. -/
theorem of_henselianLocalRing_of_isIntegral_of_isDomain
    {R S : Type u} [CommRing R] [CommRing S] [HenselianLocalRing R]
    [Algebra R S] [Algebra.IsIntegral R S] [IsDomain S] :
    IsLocalRing S := by
  classical
  refine of_isUnit_or_isUnit_one_sub_self fun a ↦ ?_
  by_contra hcon
  obtain ⟨ha, ha1⟩ := not_or.mp hcon
  -- There exists a monic annihilator of `a`; consider one of minimal degree.
  have hex : ∃ n : ℕ, ∃ F : R[X], F.Monic ∧ aeval a F = 0 ∧ F.natDegree = n := by
    obtain ⟨F, hFm, hFe⟩ := Algebra.IsIntegral.isIntegral (R := R) a
    exact ⟨F.natDegree, F, hFm, by rwa [aeval_def], rfl⟩
  obtain ⟨F, hFm, hFa, hFd⟩ := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hFd
    rw [hFm.natDegree_eq_zero.mp hFd, map_one] at hFa
    exact one_ne_zero hFa
  -- Both `F.eval 0` and `F.eval 1` lie in the maximal ideal of `R`.
  have hev (c : R) (hc : ¬IsUnit (a - algebraMap R S c)) : F.eval c ∈ maximalIdeal R := by
    by_contra hmem
    have hu : IsUnit (F.eval c) := by
      by_contra h2
      exact hmem ((mem_maximalIdeal _).mpr h2)
    obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (a := c) (p := F)
    have heq := congrArg (aeval a) hq
    rw [map_sub, hFa, aeval_C, zero_sub, map_mul, map_sub, aeval_X, aeval_C] at heq
    have hdvd : a - algebraMap R S c ∣ algebraMap R S (F.eval c) :=
      ⟨-aeval a q, by rw [mul_neg, ← heq, neg_neg]⟩
    exact hc (isUnit_of_dvd_unit hdvd (hu.map (algebraMap R S)))
  have h0 : F.eval 0 ∈ maximalIdeal R := hev 0 (by simpa using ha)
  have h1 : F.eval 1 ∈ maximalIdeal R := by
    refine hev 1 ?_
    rw [map_one, show a - 1 = -(1 - a) by ring, IsUnit.neg_iff]
    exact ha1
  -- Pass to the residue field and split off the root part at `0`.
  set κ := (maximalIdeal R).ResidueField
  set Fb := F.map (algebraMap R κ) with hFbdef
  have hFbm : Fb.Monic := hFm.map _
  have hFbdeg : Fb.natDegree = Nat.find hex := by rwa [hFbdef, hFm.natDegree_map]
  have hFb0 : Fb.eval 0 = 0 := by
    have hh : Fb.eval (algebraMap R κ 0) = algebraMap R κ (F.eval 0) := by
      rw [hFbdef, eval_map, eval₂_at_apply]
    rw [map_zero] at hh
    rwa [hh, Ideal.algebraMap_residueField_eq_zero]
  have hFb1 : Fb.eval 1 = 0 := by
    have hh : Fb.eval (algebraMap R κ 1) = algebraMap R κ (F.eval 1) := by
      rw [hFbdef, eval_map, eval₂_at_apply]
    rw [map_one] at hh
    rwa [hh, Ideal.algebraMap_residueField_eq_zero]
  have hFbne : Fb ≠ 0 := hFbm.ne_zero
  set ℓ := Fb.rootMultiplicity 0
  set gb := Fb /ₘ (X - C 0) ^ ℓ
  have hsplit : (X - C 0) ^ ℓ * gb = Fb := Fb.pow_mul_divByMonic_rootMultiplicity_eq 0
  have hXC : (X - C (0 : κ)) = X := by rw [map_zero, sub_zero]
  rw [hXC] at hsplit
  have hgbm : gb.Monic := (monic_X_pow ℓ).of_mul_monic_left (by rwa [hsplit])
  have hgb0 : gb.eval 0 ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero 0 hFbne
  have hℓpos : 0 < ℓ := (rootMultiplicity_pos hFbne).mpr hFb0
  have hgb1 : gb.eval 1 = 0 := by
    have hh := congrArg (eval 1) hsplit
    rwa [eval_mul, eval_pow, eval_X, one_pow, one_mul, hFb1] at hh
  have hgbdeg : gb.natDegree ≠ 0 := by
    intro hdeg0
    rw [hgbm.natDegree_eq_zero.mp hdeg0] at hgb1
    simp at hgb1
  -- `X ^ ℓ` and `gb` are coprime.
  have hcoX : IsCoprime (X : κ[X]) gb := by
    have hXdvd : (X : κ[X]) ∣ gb - C (gb.eval 0) := by
      rw [X_dvd_iff]
      simp [coeff_zero_eq_eval_zero]
    obtain ⟨q, hq⟩ := hXdvd
    refine ⟨-(C (gb.eval 0)⁻¹ * q), C (gb.eval 0)⁻¹, ?_⟩
    have hsub : gb - X * q = C (gb.eval 0) := by
      rw [← hq]
      ring
    calc -(C (gb.eval 0)⁻¹ * q) * X + C (gb.eval 0)⁻¹ * gb
        = C (gb.eval 0)⁻¹ * (gb - X * q) := by ring
      _ = C (gb.eval 0)⁻¹ * C (gb.eval 0) := by rw [hsub]
      _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hgb0, C_1]
  have hcop : IsCoprime ((X : κ[X]) ^ ℓ) gb := hcoX.pow_left
  -- Lift the factorization to `R` and contradict minimality.
  obtain ⟨p₁, p₂, hp₁m, hp₂m, hpe, hr₁, hr₂⟩ :=
    HenselianLocalRing.exists_monic_mul_of_map_eq_mul hFm (monic_X_pow ℓ) hgbm hsplit.symm hcop
  have hd₁ : p₁.natDegree = ℓ := by
    rw [← hp₁m.natDegree_map (algebraMap R κ), hr₁, natDegree_X_pow]
  have hd₂ : p₂.natDegree = gb.natDegree := by
    rw [← hp₂m.natDegree_map (algebraMap R κ), hr₂]
  have hsum : ℓ + gb.natDegree = Nat.find hex := by
    rw [← hFbdeg, ← hsplit, natDegree_mul (monic_X_pow ℓ).ne_zero hgbm.ne_zero, natDegree_X_pow]
  have hzero : aeval a p₁ * aeval a p₂ = 0 := by
    rw [← map_mul, ← hpe, hFa]
  rcases mul_eq_zero.mp hzero with hz | hz
  · exact Nat.find_min hex (m := p₁.natDegree) (by omega) ⟨p₁, hp₁m, hz, rfl⟩
  · exact Nat.find_min hex (m := p₂.natDegree) (by omega) ⟨p₂, hp₂m, hz, rfl⟩

end IsLocalRing

namespace Algebra

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-- The residue field extension induced by a local integral homomorphism of local rings is
algebraic. -/
theorem IsAlgebraic.residueField_of_isIntegral [Algebra.IsIntegral R S] :
    Algebra.IsAlgebraic (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := by
  -- It suffices to show that `κ(S)` is integral over `R`: since `S` is integral over `R`
  -- and `κ(S)` is integral over `S` (the map `S → κ(S)` is surjective), the composition
  -- `R → S → κ(S)` is integral.  Integrality then descends along the surjection `R → κ(R)`,
  -- so `κ(S)` is integral, hence algebraic, over `κ(R)`.
  have : Algebra.IsIntegral S (IsLocalRing.ResidueField S) :=
    Algebra.isIntegral_of_surjective IsLocalRing.residue_surjective
  have : Algebra.IsIntegral R (IsLocalRing.ResidueField S) := Algebra.IsIntegral.trans S
  have : Algebra.IsIntegral (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    Algebra.IsIntegral.tower_top R
  infer_instance

variable (R S) in
/-- Let `R → S` and `R → T` be local ring homomorphisms of local rings, with `R → S`
integral.  If `κ(S)/κ(R)` or `κ(T)/κ(R)` is purely inseparable, the tensor product
`S ⊗[R] T` is a local ring.

[Stacks 092Y](https://stacks.math.columbia.edu/tag/092Y). -/
theorem isLocalRing_tensorProduct_of_isPurelyInseparable_residueField
    (T : Type u) [CommRing T] [Algebra R T] [IsLocalRing T] [IsLocalHom (algebraMap R T)]
    [Algebra.IsIntegral R S]
    (h : IsPurelyInseparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) ∨
        IsPurelyInseparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField T)) :
    IsLocalRing (S ⊗[R] T) :=
  sorry

end Algebra
