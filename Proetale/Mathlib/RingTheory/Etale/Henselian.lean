/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Sections and factorizations over Henselian local rings

Let `R` be a Henselian local ring with residue field `κ`. In this file we prove two
consequences of the local structure of étale algebras (see
[Stacks 04GG](https://stacks.math.columbia.edu/tag/04GG)):

* `HenselianLocalRing.exists_algHom_section`: every étale `R`-algebra `R'` equipped with an
  `R`-algebra map `χ : R' → κ` admits an `R`-algebra section `σ : R' → R` compatible with `χ`.
  This is one implication of [Stacks 04GG (7)].
* `HenselianLocalRing.exists_monic_mul_of_map_eq_mul`: **Hensel's lemma for coprime
  factorizations.** A coprime factorization of a monic polynomial over `κ` lifts to a monic
  factorization over `R`. This is one implication of [Stacks 04GG (3)].

The key ingredient is `HenselianLocalRing.exists_hasMap_of_hasMap_residueField`: a point of a
standard étale pair over `R` with values in `κ` lifts to a point with values in `R`, which is
a direct application of the Hensel property.
-/

universe u

namespace HenselianLocalRing

section Factorization

open Polynomial IsLocalRing

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

/-- A point of a standard etale pair over a Henselian local ring `R` with values in the
residue field lifts to a point with values in `R`. -/
theorem exists_hasMap_of_hasMap_residueField (P : StandardEtalePair R)
    {x : (maximalIdeal R).ResidueField} (hx : P.HasMap x) :
    ∃ a : R, P.HasMap a ∧ algebraMap R (maximalIdeal R).ResidueField a = x := by
  have H := (HenselianLocalRing.TFAE R).out 0 2
  obtain ⟨a, hroot, ha⟩ := H.mp ‹HenselianLocalRing R›
    (algebraMap R (maximalIdeal R).ResidueField)
    (Ideal.algebraMap_residueField_surjective _) P.f P.monic_f x
    (by rw [← aeval_def]; exact hx.1)
    (by rw [← aeval_def]; exact hx.isUnit_derivative_f.ne_zero)
  refine ⟨a, ⟨?_, ?_⟩, ha⟩
  · rw [coe_aeval_eq_eval]
    exact hroot
  · rw [← notMem_maximalIdeal, ← Ideal.algebraMap_residueField_eq_zero, coe_aeval_eq_eval,
      ← aeval_algebraMap_apply_eq_algebraMap_eval, ha]
    exact hx.2.ne_zero

/-- A Henselian local ring admits sections of étale algebras pointed over the residue
field. This is one implication of [Stacks 04GG (7)]
(https://stacks.math.columbia.edu/tag/04GG). -/
theorem exists_algHom_section {R' : Type u} [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
    (χ : R' →ₐ[R] (maximalIdeal R).ResidueField) :
    ∃ σ : R' →ₐ[R] R,
      (IsScalarTower.toAlgHom R R (maximalIdeal R).ResidueField).comp σ = χ := by
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
  let χₗ : Localization.Away h →ₐ[R] (maximalIdeal R).ResidueField :=
    IsLocalization.liftAlgHom (M := Submonoid.powers h) (f := χ) hu
  have hχₗ : ∀ y : R', χₗ (algebraMap R' (Localization.Away h) y) = χ y := fun y ↦
    IsLocalization.lift_eq hu y
  obtain ⟨Pres⟩ := hstd.nonempty_standardEtalePresentation
  obtain ⟨a, ha, hares⟩ := exists_hasMap_of_hasMap_residueField Pres.P (Pres.hasMap.map χₗ)
  let σ₀ : Localization.Away h →ₐ[R] R := (Pres.P.lift a ha).comp Pres.equivRing.toAlgHom
  have key : (IsScalarTower.toAlgHom R R (maximalIdeal R).ResidueField).comp σ₀ = χₗ := by
    refine Pres.hom_ext ?_
    have hx : σ₀ Pres.x = a := by
      simp only [σ₀, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, Pres.equivRing_x,
        StandardEtalePair.lift_X]
    rw [AlgHom.comp_apply, hx, IsScalarTower.coe_toAlgHom', hares]
  refine ⟨σ₀.comp (IsScalarTower.toAlgHom R R' (Localization.Away h)), ?_⟩
  rw [← AlgHom.comp_assoc, key]
  ext y
  exact hχₗ y

/-- **Hensel's lemma for coprime factorizations.**  Over a Henselian local ring, a
factorization of a monic polynomial into coprime monic factors over the residue field
lifts to a factorization into monic factors.

This is one implication of [Stacks 04GG (3)](https://stacks.math.columbia.edu/tag/04GG). -/
theorem exists_monic_mul_of_map_eq_mul
    {p : R[X]} (hp : p.Monic)
    {f g : Polynomial (maximalIdeal R).ResidueField}
    (hf : f.Monic) (hg : g.Monic)
    (H : p.map (algebraMap R (maximalIdeal R).ResidueField) = f * g)
    (hco : IsCoprime f g) :
    ∃ p₁ p₂ : R[X], p₁.Monic ∧ p₂.Monic ∧ p = p₁ * p₂ ∧
      p₁.map (algebraMap R (maximalIdeal R).ResidueField) = f ∧
      p₂.map (algebraMap R (maximalIdeal R).ResidueField) = g := by
  obtain ⟨R', _, _, _, Q, _, _, f', g', hbij, hf'm, hg'm, hmul, -, hfres, hgres⟩ :=
    Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime
      (maximalIdeal R) p f g hp hf hg H hco
  let e : (maximalIdeal R).ResidueField ≃ₐ[R] Q.ResidueField :=
    AlgEquiv.ofBijective _ hbij
  let χ : R' →ₐ[R] (maximalIdeal R).ResidueField :=
    e.symm.toAlgHom.comp (IsScalarTower.toAlgHom R R' Q.ResidueField)
  obtain ⟨σ, hσ⟩ := exists_algHom_section χ
  have hσ' : (algebraMap R (maximalIdeal R).ResidueField).comp σ.toRingHom
      = χ.toRingHom := congrArg AlgHom.toRingHom hσ
  have hid : (e.symm.toAlgHom.toRingHom).comp
      (Ideal.ResidueField.mapₐ (maximalIdeal R) Q (Algebra.ofId R R')
        (Ideal.over_def Q (maximalIdeal R))).toRingHom = RingHom.id _ := by
    have hcoe : (Ideal.ResidueField.mapₐ (maximalIdeal R) Q (Algebra.ofId R R')
        (Ideal.over_def Q (maximalIdeal R))).toRingHom = e.toAlgHom.toRingHom := rfl
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
