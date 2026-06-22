/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Proetale.Mathlib.RingTheory.Henselian

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
* `HenselianLocalRing.exists_monic_mul_of_map_eq_mul`: Hensel's lemma for coprime
  factorizations: a coprime factorization over the residue field of a monic polynomial
  over a Henselian local ring lifts.
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

section Factorization

open Polynomial IsLocalRing

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

/-- A point of a standard étale pair over a Henselian local ring `R` with values in the
residue field lifts to a point with values in `R`. -/
theorem exists_hasMap_of_hasMap_residueField (P : StandardEtalePair R)
    {x : (IsLocalRing.maximalIdeal R).ResidueField} (hx : P.HasMap x) :
    ∃ a : R, P.HasMap a ∧ algebraMap R (IsLocalRing.maximalIdeal R).ResidueField a = x := by
  obtain ⟨a₀, rfl⟩ := Ideal.algebraMap_residueField_surjective (IsLocalRing.maximalIdeal R) x
  have key : ∀ q : R[X],
      Polynomial.aeval (algebraMap R (IsLocalRing.maximalIdeal R).ResidueField a₀) q
        = algebraMap R (IsLocalRing.maximalIdeal R).ResidueField (q.eval a₀) := fun q ↦
    Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval a₀ q
  have hf0 : P.f.eval a₀ ∈ IsLocalRing.maximalIdeal R := by
    rw [← Ideal.algebraMap_residueField_eq_zero (I := IsLocalRing.maximalIdeal R), ← key]
    exact hx.1
  have hf' : IsUnit (P.f.derivative.eval a₀) := by
    have hd := hx.isUnit_derivative_f
    rw [key] at hd
    by_contra hcon
    have hmem : P.f.derivative.eval a₀ ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal _).mpr hcon
    rw [Ideal.algebraMap_residueField_eq_zero.mpr hmem] at hd
    exact not_isUnit_zero hd
  obtain ⟨a, hroot, hsub⟩ := HenselianLocalRing.is_henselian P.f P.monic_f a₀ hf0 hf'
  have hres : algebraMap R (IsLocalRing.maximalIdeal R).ResidueField a
      = algebraMap R (IsLocalRing.maximalIdeal R).ResidueField a₀ := by
    rw [← sub_eq_zero, ← map_sub, Ideal.algebraMap_residueField_eq_zero]
    exact hsub
  refine ⟨a, ⟨?_, ?_⟩, hres⟩
  · rw [show Polynomial.aeval a P.f = P.f.eval a from congrFun (Polynomial.coe_aeval_eq_eval a) _]
    exact hroot
  · rw [show Polynomial.aeval a P.g = P.g.eval a from congrFun (Polynomial.coe_aeval_eq_eval a) _]
    by_contra hcon
    have hmem : P.g.eval a ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal _).mpr hcon
    have h2 : algebraMap R (IsLocalRing.maximalIdeal R).ResidueField (P.g.eval a) = 0 :=
      Ideal.algebraMap_residueField_eq_zero.mpr hmem
    have h3 := hx.2
    rw [key] at h3
    have h4 : algebraMap R (IsLocalRing.maximalIdeal R).ResidueField (P.g.eval a)
        = algebraMap R (IsLocalRing.maximalIdeal R).ResidueField (P.g.eval a₀) := by
      rw [← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
        ← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hres]
    rw [← h4, h2] at h3
    exact not_isUnit_zero h3

/-- A Henselian local ring admits sections of étale algebras pointed over the residue
field. This is one implication of [Stacks 04GG (7)]
(https://stacks.math.columbia.edu/tag/04GG). -/
theorem exists_algHom_section {R' : Type u} [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
    (χ : R' →ₐ[R] (IsLocalRing.maximalIdeal R).ResidueField) :
    ∃ σ : R' →ₐ[R] R,
      ∀ y, algebraMap R (IsLocalRing.maximalIdeal R).ResidueField (σ y) = χ y := by
  classical
  have hQp : (RingHom.ker χ.toRingHom).IsPrime := RingHom.ker_isPrime _
  have hFE : Algebra.FormallyEtale R (Localization.AtPrime (RingHom.ker χ.toRingHom)) :=
    inferInstanceAs (Algebra.FormallyEtale R (Localization (RingHom.ker χ.toRingHom).primeCompl))
  have hEt : Algebra.IsEtaleAt R (RingHom.ker χ.toRingHom) := hFE
  obtain ⟨h, hhQ, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R)
    (RingHom.ker χ.toRingHom)
  have hu : ∀ y : Submonoid.powers h, IsUnit (χ y) := by
    rintro ⟨y, n, rfl⟩
    rw [map_pow]
    refine IsUnit.pow _ ?_
    rw [isUnit_iff_ne_zero]
    exact fun e ↦ hhQ (RingHom.mem_ker.mpr e)
  let χₗ : Localization.Away h →ₐ[R] (IsLocalRing.maximalIdeal R).ResidueField :=
    IsLocalization.liftAlgHom (M := Submonoid.powers h) (f := χ) hu
  have hχₗ : ∀ y : R', χₗ (algebraMap R' (Localization.Away h) y) = χ y := fun y ↦
    IsLocalization.lift_eq hu y
  obtain ⟨Pres⟩ := hstd.nonempty_standardEtalePresentation
  obtain ⟨a, ha, hares⟩ := exists_hasMap_of_hasMap_residueField Pres.P (Pres.hasMap.map χₗ)
  let σ₀ : Localization.Away h →ₐ[R] R := (Pres.P.lift a ha).comp Pres.equivRing.toAlgHom
  have key : (IsScalarTower.toAlgHom R R (IsLocalRing.maximalIdeal R).ResidueField).comp σ₀
      = χₗ := by
    refine Pres.hom_ext ?_
    change algebraMap R (IsLocalRing.maximalIdeal R).ResidueField (σ₀ Pres.x) = χₗ Pres.x
    have hx : σ₀ Pres.x = a := by
      change (Pres.P.lift a ha) (Pres.equivRing Pres.x) = a
      rw [Pres.equivRing_x, Pres.P.lift_X]
    rw [hx, hares]
  refine ⟨σ₀.comp (IsScalarTower.toAlgHom R R' (Localization.Away h)), fun y ↦ ?_⟩
  calc algebraMap R (IsLocalRing.maximalIdeal R).ResidueField
        (σ₀ (algebraMap R' (Localization.Away h) y))
      = ((IsScalarTower.toAlgHom R R (IsLocalRing.maximalIdeal R).ResidueField).comp σ₀)
          (algebraMap R' (Localization.Away h) y) := rfl
    _ = χₗ (algebraMap R' (Localization.Away h) y) := by rw [key]
    _ = χ y := hχₗ y

/-- **Hensel's lemma for coprime factorizations.**  Over a Henselian local ring, a
factorization of a monic polynomial into coprime monic factors over the residue field
lifts to a factorization into monic factors.

This is one implication of [Stacks 04GG (3)](https://stacks.math.columbia.edu/tag/04GG). -/
theorem exists_monic_mul_of_map_eq_mul
    {p : R[X]} (hp : p.Monic)
    {f g : Polynomial (IsLocalRing.maximalIdeal R).ResidueField}
    (hf : f.Monic) (hg : g.Monic)
    (H : p.map (algebraMap R (IsLocalRing.maximalIdeal R).ResidueField) = f * g)
    (hco : IsCoprime f g) :
    ∃ p₁ p₂ : R[X], p₁.Monic ∧ p₂.Monic ∧ p = p₁ * p₂ ∧
      p₁.map (algebraMap R (IsLocalRing.maximalIdeal R).ResidueField) = f ∧
      p₂.map (algebraMap R (IsLocalRing.maximalIdeal R).ResidueField) = g := by
  obtain ⟨R', _, _, _, Q, _, _, f', g', hbij, hf'm, hg'm, hmul, -, hfres, hgres⟩ :=
    Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime
      (IsLocalRing.maximalIdeal R) p f g hp hf hg H hco
  let e : (IsLocalRing.maximalIdeal R).ResidueField ≃ₐ[R] Q.ResidueField :=
    AlgEquiv.ofBijective _ hbij
  let χ : R' →ₐ[R] (IsLocalRing.maximalIdeal R).ResidueField :=
    e.symm.toAlgHom.comp (IsScalarTower.toAlgHom R R' Q.ResidueField)
  obtain ⟨σ, hσ⟩ := exists_algHom_section χ
  have hσ' : (algebraMap R (IsLocalRing.maximalIdeal R).ResidueField).comp σ.toRingHom
      = χ.toRingHom := RingHom.ext hσ
  have hid : (e.symm.toAlgHom.toRingHom).comp
      (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) Q (Algebra.ofId R R')
        (Ideal.over_def Q (IsLocalRing.maximalIdeal R))).toRingHom = RingHom.id _ := by
    have hcoe : (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) Q (Algebra.ofId R R')
        (Ideal.over_def Q (IsLocalRing.maximalIdeal R))).toRingHom = e.toAlgHom.toRingHom := rfl
    rw [hcoe]
    ext z
    simp
  have hχ : χ.toRingHom = (e.symm.toAlgHom.toRingHom).comp (algebraMap R' Q.ResidueField) := rfl
  refine ⟨f'.map σ.toRingHom, g'.map σ.toRingHom, hf'm.map _, hg'm.map _, ?_, ?_, ?_⟩
  · have hcomp : σ.toRingHom.comp (algebraMap R R') = RingHom.id R := by
      ext r
      simp
    have hh := congrArg (Polynomial.map σ.toRingHom) hmul
    rwa [Polynomial.map_map, hcomp, Polynomial.map_id, Polynomial.map_mul] at hh
  · rw [Polynomial.map_map, hσ', hχ, ← Polynomial.map_map, ← hfres, Polynomial.map_map, hid,
      Polynomial.map_id]
  · rw [Polynomial.map_map, hσ', hχ, ← Polynomial.map_map, ← hgres, Polynomial.map_map, hid,
      Polynomial.map_id]

end Factorization

end HenselianLocalRing

namespace IsLocalRing

open Polynomial

/-- An integral algebra over a Henselian local ring that is an integral domain is local. -/
theorem of_henselianLocalRing_of_isIntegral_of_isDomain
    {R S : Type u} [CommRing R] [CommRing S] [HenselianLocalRing R]
    [Algebra R S] [Algebra.IsIntegral R S] [IsDomain S] :
    IsLocalRing S := by
  classical
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a ↦ ?_
  by_contra hcon
  obtain ⟨ha, ha1⟩ := not_or.mp hcon
  -- There exists a monic annihilator of `a`; consider one of minimal degree.
  have hex : ∃ n : ℕ, ∃ F : R[X], F.Monic ∧ Polynomial.aeval a F = 0 ∧ F.natDegree = n := by
    obtain ⟨F, hFm, hFe⟩ := Algebra.IsIntegral.isIntegral (R := R) a
    exact ⟨F.natDegree, F, hFm, by rwa [Polynomial.aeval_def], rfl⟩
  obtain ⟨F, hFm, hFa, hFd⟩ := Nat.find_spec hex
  have hmin : ∀ m, m < Nat.find hex →
      ¬∃ F : R[X], F.Monic ∧ Polynomial.aeval a F = 0 ∧ F.natDegree = m := fun m hm ↦
    Nat.find_min hex hm
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hFd
    rw [hFm.natDegree_eq_zero.mp hFd, map_one] at hFa
    exact one_ne_zero hFa
  -- Both `F.eval 0` and `F.eval 1` lie in the maximal ideal of `R`.
  have hev : ∀ c : R, ¬IsUnit (a - algebraMap R S c) →
      F.eval c ∈ IsLocalRing.maximalIdeal R := by
    intro c hc
    by_contra hmem
    have hu : IsUnit (F.eval c) := by
      by_contra h2
      exact hmem ((IsLocalRing.mem_maximalIdeal _).mpr h2)
    obtain ⟨q, hq⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := c) (p := F)
    have heq := congrArg (Polynomial.aeval a) hq
    rw [map_sub, hFa, Polynomial.aeval_C, zero_sub, map_mul, map_sub, Polynomial.aeval_X,
      Polynomial.aeval_C] at heq
    have hdvd : a - algebraMap R S c ∣ algebraMap R S (F.eval c) :=
      ⟨-Polynomial.aeval a q, by rw [mul_neg, ← heq, neg_neg]⟩
    exact hc (isUnit_of_dvd_unit hdvd (hu.map (algebraMap R S)))
  have h0 : F.eval 0 ∈ IsLocalRing.maximalIdeal R := hev 0 (by simpa using ha)
  have h1 : F.eval 1 ∈ IsLocalRing.maximalIdeal R := by
    refine hev 1 ?_
    rw [map_one, show a - 1 = -(1 - a) by ring, IsUnit.neg_iff]
    exact ha1
  -- Pass to the residue field and split off the root part at `0`.
  set κ := (IsLocalRing.maximalIdeal R).ResidueField with hκdef
  set Fb := F.map (algebraMap R κ) with hFbdef
  have hFbm : Fb.Monic := hFm.map _
  have hFbdeg : Fb.natDegree = Nat.find hex := by rw [hFbdef, hFm.natDegree_map]; exact hFd
  have hFb0 : Fb.eval 0 = 0 := by
    have hh : Fb.eval (algebraMap R κ 0) = algebraMap R κ (F.eval 0) := by
      rw [hFbdef, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    rw [map_zero] at hh
    rw [hh, Ideal.algebraMap_residueField_eq_zero]
    exact h0
  have hFb1 : Fb.eval 1 = 0 := by
    have hh : Fb.eval (algebraMap R κ 1) = algebraMap R κ (F.eval 1) := by
      rw [hFbdef, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    rw [map_one] at hh
    rw [hh, Ideal.algebraMap_residueField_eq_zero]
    exact h1
  have hFbne : Fb ≠ 0 := hFbm.ne_zero
  set ℓ := Fb.rootMultiplicity 0 with hℓdef
  set gb := Fb /ₘ (X - C 0) ^ ℓ with hgbdef
  have hsplit : (X - C 0) ^ ℓ * gb = Fb := Fb.pow_mul_divByMonic_rootMultiplicity_eq 0
  have hXC : (X - C (0 : κ)) = X := by rw [map_zero, sub_zero]
  rw [hXC] at hsplit
  have hgbm : gb.Monic :=
    (Polynomial.monic_X_pow ℓ).of_mul_monic_left (by rw [hsplit]; exact hFbm)
  have hgb0 : gb.eval 0 ≠ 0 :=
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero 0 hFbne
  have hℓpos : 0 < ℓ := (Polynomial.rootMultiplicity_pos hFbne).mpr hFb0
  have hgb1 : gb.eval 1 = 0 := by
    have hh := congrArg (Polynomial.eval 1) hsplit
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, one_pow, one_mul, hFb1] at hh
    exact hh
  have hgbdeg : gb.natDegree ≠ 0 := by
    intro hdeg0
    rw [hgbm.natDegree_eq_zero.mp hdeg0] at hgb1
    simp at hgb1
  -- `X ^ ℓ` and `gb` are coprime.
  have hcoX : IsCoprime (Polynomial.X : κ[X]) gb := by
    have hXdvd : (Polynomial.X : κ[X]) ∣ gb - C (gb.eval 0) := by
      rw [Polynomial.X_dvd_iff]
      simp [Polynomial.coeff_zero_eq_eval_zero]
    obtain ⟨q, hq⟩ := hXdvd
    refine ⟨-(C (gb.eval 0)⁻¹ * q), C (gb.eval 0)⁻¹, ?_⟩
    have hsub : gb - Polynomial.X * q = C (gb.eval 0) := by
      rw [← hq]; ring
    calc -(C (gb.eval 0)⁻¹ * q) * Polynomial.X + C (gb.eval 0)⁻¹ * gb
        = C (gb.eval 0)⁻¹ * (gb - Polynomial.X * q) := by ring
      _ = C (gb.eval 0)⁻¹ * C (gb.eval 0) := by rw [hsub]
      _ = 1 := by rw [← Polynomial.C_mul, inv_mul_cancel₀ hgb0, Polynomial.C_1]
  have hcop : IsCoprime ((Polynomial.X : κ[X]) ^ ℓ) gb := hcoX.pow_left
  -- Lift the factorization to `R` and contradict minimality.
  obtain ⟨p₁, p₂, hp₁m, hp₂m, hpe, hr₁, hr₂⟩ :=
    HenselianLocalRing.exists_monic_mul_of_map_eq_mul hFm (Polynomial.monic_X_pow ℓ) hgbm
      hsplit.symm hcop
  have hd₁ : p₁.natDegree = ℓ := by
    rw [← hp₁m.natDegree_map (algebraMap R κ), hr₁, Polynomial.natDegree_X_pow]
  have hd₂ : p₂.natDegree = gb.natDegree := by
    rw [← hp₂m.natDegree_map (algebraMap R κ), hr₂]
  have hsum : ℓ + gb.natDegree = Nat.find hex := by
    rw [← hFbdeg, ← hsplit, Polynomial.natDegree_mul (Polynomial.monic_X_pow ℓ).ne_zero
      hgbm.ne_zero, Polynomial.natDegree_X_pow]
  have hzero : Polynomial.aeval a p₁ * Polynomial.aeval a p₂ = 0 := by
    rw [← map_mul, ← hpe, hFa]
  rcases mul_eq_zero.mp hzero with hz | hz
  · exact hmin p₁.natDegree (by omega) ⟨p₁, hp₁m, hz, rfl⟩
  · exact hmin p₂.natDegree (by omega) ⟨p₂, hp₂m, hz, rfl⟩

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

section TensorProduct

open IsLocalRing

/-- A commutative ring whose prime spectrum is a singleton is local. -/
private theorem isLocalRing_of_primeSpectrum {A : Type*} [CommRing A]
    (h₁ : Nonempty (PrimeSpectrum A)) (h₂ : Subsingleton (PrimeSpectrum A)) :
    IsLocalRing A := by
  obtain ⟨p⟩ := h₁
  have : Nontrivial A :=
    ⟨0, 1, fun e ↦ p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (e ▸ p.asIdeal.zero_mem))⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  refine IsLocalRing.of_unique_max_ideal ⟨m, hm, fun J hJ ↦ ?_⟩
  exact congrArg PrimeSpectrum.asIdeal (h₂.elim ⟨J, hJ.isPrime⟩ ⟨m, hm.isPrime⟩)

/-- If `L` is a purely inseparable extension of the residue field of a local ring `R` and
`K` is an `R`-field killed by the maximal ideal, then `L ⊗[R] K` is a local ring. -/
private theorem isLocalRing_tensorProduct_of_isPurelyInseparable_left
    (R : Type u) [CommRing R] [IsLocalRing R]
    (L K : Type u) [Field L] [Field K] [Algebra R L] [Algebra R K]
    [Algebra (ResidueField R) L] [IsScalarTower R (ResidueField R) L]
    [IsPurelyInseparable (ResidueField R) L]
    (hK : ∀ x ∈ maximalIdeal R, algebraMap R K x = 0) :
    IsLocalRing (L ⊗[R] K) := by
  -- `κ(R) ⊗[R] K ≃ K` since `K` is killed by the maximal ideal.
  let u : ResidueField R →ₐ[R] K :=
    Ideal.Quotient.liftₐ (maximalIdeal R) (Algebra.ofId R K) hK
  let Φ : (ResidueField R) ⊗[R] K →ₐ[R] K := Algebra.TensorProduct.productMap u (AlgHom.id R K)
  have htmul : ∀ z : (ResidueField R) ⊗[R] K, ∃ x : K, z = 1 ⊗ₜ[R] x := by
    intro z
    induction z with
    | zero => exact ⟨0, (TensorProduct.tmul_zero _ _).symm⟩
    | tmul r x =>
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
      refine ⟨algebraMap R K r * x, ?_⟩
      rw [show (IsLocalRing.residue R r : ResidueField R) = r • (1 : ResidueField R) by
            rw [Algebra.smul_def, mul_one]; rfl,
        TensorProduct.smul_tmul, Algebra.smul_def]
    | add z₁ z₂ h₁ h₂ =>
      obtain ⟨x₁, rfl⟩ := h₁
      obtain ⟨x₂, rfl⟩ := h₂
      exact ⟨x₁ + x₂, (TensorProduct.tmul_add _ _ _).symm⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro z w hzw
      obtain ⟨x, rfl⟩ := htmul z
      obtain ⟨y, rfl⟩ := htmul w
      have hxy : x = y := by simpa [Φ] using hzw
      rw [hxy]
    · intro x
      exact ⟨1 ⊗ₜ x, by simp [Φ]⟩
  let e : (ResidueField R) ⊗[R] K ≃ₐ[R] K := AlgEquiv.ofBijective Φ hΦ
  have h1 : IsHomeomorph (PrimeSpectrum.comap (Algebra.TensorProduct.map
      (Algebra.ofId (ResidueField R) L) (AlgHom.id R K)).toRingHom) :=
    PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable
      (K := ResidueField R) (R := R) (S := K) L
  have h2 : Function.Bijective
      (PrimeSpectrum.comap (e.toRingEquiv : (ResidueField R) ⊗[R] K ≃+* K).toRingHom) :=
    (PrimeSpectrum.isHomeomorph_comap_of_bijective e.toRingEquiv.bijective).bijective
  have hsub : Subsingleton (PrimeSpectrum ((ResidueField R) ⊗[R] K)) :=
    h2.surjective.subsingleton
  have hne : Nonempty (PrimeSpectrum ((ResidueField R) ⊗[R] K)) := by
    obtain ⟨q⟩ : Nonempty (PrimeSpectrum K) := inferInstance
    exact ⟨PrimeSpectrum.comap (e.toRingEquiv : _ ≃+* K).toRingHom q⟩
  refine isLocalRing_of_primeSpectrum ?_ (h1.bijective.injective.subsingleton)
  obtain ⟨q⟩ := hne
  obtain ⟨p, -⟩ := h1.bijective.surjective q
  exact ⟨p⟩

variable (R S) in
private theorem isLocalRing_tensorProduct_aux
    (T : Type u) [CommRing T] [Algebra R T] [IsLocalRing T] [IsLocalHom (algebraMap R T)]
    [Algebra.IsIntegral R S]
    (h : IsPurelyInseparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) ∨
        IsPurelyInseparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField T)) :
    IsLocalRing (T ⊗[R] S) := by
  classical
  -- the residue fields of `S` and `T` are killed by the maximal ideal of `R`
  have hkill : ∀ (W : Type u) [CommRing W] [Algebra R W] [IsLocalRing W]
      [IsLocalHom (algebraMap R W)], ∀ x ∈ maximalIdeal R,
        algebraMap R (ResidueField W) x = 0 := by
    intro W _ _ _ _ x hx
    rw [IsScalarTower.algebraMap_apply R W (ResidueField W), ResidueField.algebraMap_eq,
      IsLocalRing.residue_eq_zero_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x).mp hx)
      (IsLocalHom.map_nonunit x hu)
  -- the tensor product of the residue fields is local
  have hcase : IsLocalRing ((ResidueField T) ⊗[R] (ResidueField S)) := by
    rcases h with h | h
    · haveI := h
      have hloc : IsLocalRing ((ResidueField S) ⊗[R] (ResidueField T)) :=
        isLocalRing_tensorProduct_of_isPurelyInseparable_left R (ResidueField S)
          (ResidueField T) (hkill T)
      exact (Algebra.TensorProduct.comm R (ResidueField S)
        (ResidueField T)).toRingEquiv.isLocalRing
    · haveI := h
      exact isLocalRing_tensorProduct_of_isPurelyInseparable_left R (ResidueField T)
        (ResidueField S) (hkill S)
  -- the two distinguished ideals of the tensor product
  set A := T ⊗[R] S with hAdef
  let inclS : S →ₐ[R] A := Algebra.TensorProduct.includeRight
  let J₂ : Ideal A := (maximalIdeal S).map inclS
  let J₁ : Ideal A := (maximalIdeal T).map (algebraMap T A)
  -- identify `A ⧸ (J₂ ⊔ J₁)` with `κ(T) ⊗[R] κ(S)`
  let e₁ : T ⊗[R] (ResidueField S) ≃ₐ[R] A ⧸ J₂ :=
    Algebra.TensorProduct.tensorQuotientEquiv R S T (maximalIdeal S)
  let I₁ : Ideal (T ⊗[R] (ResidueField S)) :=
    (maximalIdeal T).map (algebraMap T (T ⊗[R] (ResidueField S)))
  have hcomm : (e₁ : T ⊗[R] (ResidueField S) →+* A ⧸ J₂).comp
      (algebraMap T (T ⊗[R] (ResidueField S)))
      = (Ideal.Quotient.mk J₂).comp (algebraMap T A) := by
    ext t
    exact Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul (R := R) R S T
      (maximalIdeal S) t 1
  have hIJ : J₁.map (Ideal.Quotient.mk J₂)
      = I₁.map (e₁.toRingEquiv : T ⊗[R] (ResidueField S) ≃+* A ⧸ J₂) := by
    change J₁.map (Ideal.Quotient.mk J₂)
      = I₁.map (e₁ : T ⊗[R] (ResidueField S) →+* A ⧸ J₂)
    rw [Ideal.map_map, Ideal.map_map, hcomm]
  let E₂ : (T ⊗[R] (ResidueField S)) ⧸ I₁ ≃+* (A ⧸ J₂) ⧸ J₁.map (Ideal.Quotient.mk J₂) :=
    Ideal.quotientEquiv I₁ (J₁.map (Ideal.Quotient.mk J₂)) e₁.toRingEquiv hIJ
  let E₃ : (ResidueField T) ⊗[R] (ResidueField S) ≃ₐ[R] (T ⊗[R] (ResidueField S)) ⧸ I₁ :=
    Algebra.TensorProduct.quotientTensorEquiv R (ResidueField S) T (maximalIdeal T)
  let E : (ResidueField T) ⊗[R] (ResidueField S) ≃+* A ⧸ (J₂ ⊔ J₁) :=
    (E₃.toRingEquiv.trans E₂).trans (DoubleQuot.quotQuotEquivQuotSup J₂ J₁)
  have hQuot : IsLocalRing (A ⧸ (J₂ ⊔ J₁)) := E.isLocalRing
  -- every maximal ideal of `A` contains `J₂ ⊔ J₁`
  have hle : ∀ Q : Ideal A, Q.IsMaximal → J₂ ⊔ J₁ ≤ Q := by
    intro Q hQ
    haveI := hQ.isPrime
    have hT : Q.comap (algebraMap T A) = maximalIdeal T :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q)
    have hR : Q.comap (algebraMap R A) = maximalIdeal R := by
      rw [IsScalarTower.algebraMap_eq R T A, ← Ideal.comap_comap, hT,
        IsLocalRing.maximalIdeal_comap]
    have hScomap : (Q.comap inclS.toRingHom).comap (algebraMap R S) = maximalIdeal R := by
      have hcompS : inclS.toRingHom.comp (algebraMap R S) = algebraMap R A := by
        ext r
        exact inclS.commutes r
      rw [Ideal.comap_comap, hcompS, hR]
    have hSmax : (Q.comap inclS.toRingHom).IsMaximal := by
      refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R)
        (Q.comap inclS.toRingHom) ?_
      rw [hScomap]
      exact IsLocalRing.maximalIdeal.isMaximal R
    have hS : Q.comap inclS.toRingHom = maximalIdeal S := IsLocalRing.eq_maximalIdeal hSmax
    refine sup_le ?_ (Ideal.map_le_iff_le_comap.mpr hT.ge)
    have : (maximalIdeal S).map inclS.toRingHom ≤ Q := Ideal.map_le_iff_le_comap.mpr hS.ge
    exact this
  -- conclude
  have hnontriv : Nontrivial A := (Ideal.Quotient.mk (J₂ ⊔ J₁)).domain_nontrivial
  have key : ∀ Q : Ideal A, Q.IsMaximal →
      Q = (maximalIdeal (A ⧸ (J₂ ⊔ J₁))).comap (Ideal.Quotient.mk (J₂ ⊔ J₁)) := by
    intro Q hQ
    have hKQ : J₂ ⊔ J₁ ≤ Q := hle Q hQ
    have hmapne : Q.map (Ideal.Quotient.mk (J₂ ⊔ J₁)) ≠ ⊤ := by
      intro htop
      have hcm := Ideal.comap_map_of_surjective (Ideal.Quotient.mk (J₂ ⊔ J₁))
        Ideal.Quotient.mk_surjective Q
      rw [htop, Ideal.comap_top] at hcm
      have hker : Ideal.comap (Ideal.Quotient.mk (J₂ ⊔ J₁)) ⊥ = J₂ ⊔ J₁ := Ideal.mk_ker
      rw [hker] at hcm
      exact hQ.ne_top (by rw [← sup_eq_left.mpr hKQ, ← hcm])
    have hQle : Q ≤ (maximalIdeal (A ⧸ (J₂ ⊔ J₁))).comap (Ideal.Quotient.mk (J₂ ⊔ J₁)) :=
      le_trans Ideal.le_comap_map (Ideal.comap_mono (IsLocalRing.le_maximalIdeal hmapne))
    exact hQ.eq_of_le (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top) hQle
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  refine IsLocalRing.of_unique_max_ideal ⟨M, hM, fun J hJ ↦ ?_⟩
  rw [key J hJ, key M hM]

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
    IsLocalRing (S ⊗[R] T) := by
  have := isLocalRing_tensorProduct_aux R S T h
  exact (Algebra.TensorProduct.comm R T S).toRingEquiv.isLocalRing

end TensorProduct

end Algebra
