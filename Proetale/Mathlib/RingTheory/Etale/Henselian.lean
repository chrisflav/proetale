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

* `HenselianLocalRing.existsUnique_algHom_section`: every étale `R`-algebra `R'` equipped with
  an `R`-algebra map `χ : R' → κ` admits a unique `R`-algebra section `σ : R' → R` compatible
  with `χ`. This is one implication of [Stacks 04GG (7)].
* `HenselianLocalRing.exists_monic_mul_of_map_eq_mul_of_isCoprime`: **Hensel's lemma for
  coprime factorizations.** A coprime factorization of a monic polynomial over `κ` lifts to a
  monic factorization over `R`. This is one implication of [Stacks 04GG (3)].

The key ingredient is `HenselianLocalRing.existsUnique_hasMap_of_hasMap_residueField`: a point
of a standard étale pair over `R` with values in `κ` lifts uniquely to a point with values in
`R`, which is a direct application of the Hensel property.

## Implementation notes

We deliberately state the results over `(maximalIdeal R).ResidueField` (i.e.
`Ideal.ResidueField`, defined via `Localization.AtPrime`) rather than
`IsLocalRing.ResidueField R = R ⧸ maximalIdeal R`, for compatibility with the
`Ideal.LiesOver`/`Ideal.ResidueField.mapₐ` ecosystem used by
`Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime`. To transport a
statement to the quotient form, use `Ideal.bijective_algebraMap_quotient_residueField`.
-/

namespace HenselianLocalRing

open Polynomial IsLocalRing

variable {R : Type*} [CommRing R] [HenselianLocalRing R]

/-- A point of a standard étale pair over a Henselian local ring `R` with values in the
residue field lifts uniquely to a point with values in `R`.

TODO: generalize the existence part to Henselian pairs, i.e. `HenselianRing R I` with target
`R ⧸ I`, using `HenselianRing.is_henselian` and `isLocalHom_of_le_jacobson_bot`. -/
theorem existsUnique_hasMap_of_hasMap_residueField (P : StandardEtalePair R)
    {x : (maximalIdeal R).ResidueField} (hx : P.HasMap x) :
    ∃! a : R, P.HasMap a ∧ algebraMap R (maximalIdeal R).ResidueField a = x := by
  have H := (TFAE R).out 0 2
  obtain ⟨a, hroot, ha⟩ := H.mp ‹HenselianLocalRing R›
    (algebraMap R (maximalIdeal R).ResidueField)
    (Ideal.algebraMap_residueField_surjective _) P.f P.monic_f x
    (by rw [← aeval_def]; exact hx.1)
    (by rw [← aeval_def]; exact hx.isUnit_derivative_f.ne_zero)
  have hmap : P.HasMap a := by
    refine ⟨?_, ?_⟩
    · rw [coe_aeval_eq_eval]
      exact hroot
    · rw [← notMem_maximalIdeal, ← Ideal.algebraMap_residueField_eq_zero, coe_aeval_eq_eval,
        ← aeval_algebraMap_apply_eq_algebraMap_eval, ha]
      exact hx.2.ne_zero
  refine ⟨a, ⟨hmap, ha⟩, ?_⟩
  rintro b ⟨hb, hbres⟩
  have hsub : b - a ∈ maximalIdeal R := by
    rw [← Ideal.algebraMap_residueField_eq_zero, map_sub, hbres, ha, sub_self]
  refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub ?_ ?_
    (fun hu ↦ notMem_maximalIdeal.mpr hu hsub) ?_
  · rw [← coe_aeval_eq_eval]
    exact hb.1
  · rw [← coe_aeval_eq_eval]
    exact hmap.1
  · rw [← coe_aeval_eq_eval]
    exact hb.isUnit_derivative_f

/-- A Henselian local ring admits unique sections of finitely presented algebras pointed
over the residue field that are étale at the kernel of the point. This is one implication of
[Stacks 04GG (7)](https://stacks.math.columbia.edu/tag/04GG).

For the version for étale algebras, see `HenselianLocalRing.existsUnique_algHom_section`. -/
theorem existsUnique_algHom_section_of_isEtaleAt {R' : Type*} [CommRing R'] [Algebra R R']
    [Algebra.FinitePresentation R R'] (χ : R' →ₐ[R] (maximalIdeal R).ResidueField)
    [(RingHom.ker χ.toRingHom).IsPrime] [Algebra.IsEtaleAt R (RingHom.ker χ.toRingHom)] :
    ∃! σ : R' →ₐ[R] R,
      (IsScalarTower.toAlgHom R R (maximalIdeal R).ResidueField).comp σ = χ := by
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
  -- Note: do not inline `hχₗ` below; the explicit type ascription does real elaboration work
  -- and inlining it causes a deterministic `whnf` timeout.
  have hχₗ : ∀ y : R', χₗ (algebraMap R' (Localization.Away h) y) = χ y := fun y ↦
    IsLocalization.lift_eq hu y
  obtain ⟨Pres⟩ := hstd.nonempty_standardEtalePresentation
  obtain ⟨a, ⟨ha, hares⟩, huniq⟩ :=
    existsUnique_hasMap_of_hasMap_residueField Pres.P (Pres.hasMap.map χₗ)
  let σ₀ : Localization.Away h →ₐ[R] R := (Pres.P.lift a ha).comp Pres.equivRing.toAlgHom
  have hx : σ₀ Pres.x = a := by
    simp only [σ₀, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, Pres.equivRing_x,
      StandardEtalePair.lift_X]
  have key : (IsScalarTower.toAlgHom R R (maximalIdeal R).ResidueField).comp σ₀ = χₗ := by
    refine Pres.hom_ext ?_
    rw [AlgHom.comp_apply, hx, IsScalarTower.coe_toAlgHom', hares]
  refine ⟨σ₀.comp (IsScalarTower.toAlgHom R R' (Localization.Away h)), ?_, ?_⟩
  · show (IsScalarTower.toAlgHom R R (maximalIdeal R).ResidueField).comp _ = χ
    rw [← AlgHom.comp_assoc, key]
    ext y
    exact hχₗ y
  · intro σ' hσ'
    replace hσ' : (IsScalarTower.toAlgHom R R (maximalIdeal R).ResidueField).comp σ' = χ := hσ'
    have hres : ∀ y : R', algebraMap R (maximalIdeal R).ResidueField (σ' y) = χ y := fun y ↦ by
      have := DFunLike.congr_fun hσ' y
      rwa [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at this
    have hu' : ∀ y : Submonoid.powers h, IsUnit (σ' y) := by
      rintro ⟨y, n, rfl⟩
      rw [map_pow]
      refine IsUnit.pow _ ?_
      rw [← notMem_maximalIdeal, ← Ideal.algebraMap_residueField_eq_zero, hres]
      exact fun e ↦ hhQ (RingHom.mem_ker.mpr e)
    let σ'ₗ : Localization.Away h →ₐ[R] R :=
      IsLocalization.liftAlgHom (M := Submonoid.powers h) (f := σ') hu'
    have hσ'ₗ : ∀ y : R', σ'ₗ (algebraMap R' (Localization.Away h) y) = σ' y := fun y ↦
      IsLocalization.lift_eq hu' y
    have hresₗ : (IsScalarTower.toAlgHom R R (maximalIdeal R).ResidueField).comp σ'ₗ = χₗ :=
      AlgHom.coe_ringHom_injective <| IsLocalization.ringHom_ext (Submonoid.powers h) <|
        RingHom.ext fun y ↦ by
          simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom]
          rw [AlgHom.comp_apply, hσ'ₗ, IsScalarTower.coe_toAlgHom', hres, hχₗ]
    have hb : σ'ₗ Pres.x = a := by
      refine huniq _ ⟨Pres.hasMap.map σ'ₗ, ?_⟩
      have := DFunLike.congr_fun hresₗ Pres.x
      rwa [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at this
    have heq : σ'ₗ = σ₀ := Pres.hom_ext (hb.trans hx.symm)
    ext y
    rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ← heq, hσ'ₗ]

/-- A Henselian local ring admits unique sections of étale algebras pointed over the residue
field. This is one implication of [Stacks 04GG (7)]
(https://stacks.math.columbia.edu/tag/04GG). -/
theorem existsUnique_algHom_section {R' : Type*} [CommRing R'] [Algebra R R']
    [Algebra.Etale R R'] (χ : R' →ₐ[R] (maximalIdeal R).ResidueField) :
    ∃! σ : R' →ₐ[R] R,
      (IsScalarTower.toAlgHom R R (maximalIdeal R).ResidueField).comp σ = χ :=
  haveI : (RingHom.ker χ.toRingHom).IsPrime := RingHom.ker_isPrime _
  haveI : Algebra.IsEtaleAt R (RingHom.ker χ.toRingHom) :=
    inferInstanceAs (Algebra.FormallyEtale R (Localization (RingHom.ker χ.toRingHom).primeCompl))
  existsUnique_algHom_section_of_isEtaleAt χ

/-- **Hensel's lemma for coprime factorizations.** Over a Henselian local ring, a
factorization of a monic polynomial into coprime monic factors over the residue field
lifts to a factorization into monic factors.

This is one implication of [Stacks 04GG (3)](https://stacks.math.columbia.edu/tag/04GG). -/
theorem exists_monic_mul_of_map_eq_mul_of_isCoprime
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
  obtain ⟨σ, hσ, -⟩ := existsUnique_algHom_section χ
  have hσ' : (algebraMap R (maximalIdeal R).ResidueField).comp σ.toRingHom
      = χ.toRingHom := congrArg AlgHom.toRingHom hσ
  have hid : e.symm.toAlgHom.toRingHom.comp
      (Ideal.ResidueField.mapₐ (maximalIdeal R) Q (Algebra.ofId R R')
        (Ideal.over_def Q (maximalIdeal R))).toRingHom = RingHom.id _ := by
    -- `e` is by definition `AlgEquiv.ofBijective` of the `Ideal.ResidueField.mapₐ` below,
    -- so the underlying ring homomorphisms agree definitionally.
    have hcoe : (Ideal.ResidueField.mapₐ (maximalIdeal R) Q (Algebra.ofId R R')
        (Ideal.over_def Q (maximalIdeal R))).toRingHom = e.toAlgHom.toRingHom := rfl
    rw [hcoe]
    exact congrArg AlgHom.toRingHom e.symm_comp
  have hχ : χ.toRingHom = e.symm.toAlgHom.toRingHom.comp (algebraMap R' Q.ResidueField) := rfl
  refine ⟨f'.map σ.toRingHom, g'.map σ.toRingHom, hf'm.map _, hg'm.map _, ?_, ?_, ?_⟩
  · have hcomp : σ.toRingHom.comp (algebraMap R R') = RingHom.id R :=
      σ.comp_algebraMap.trans Algebra.algebraMap_self
    have hh := congrArg (Polynomial.map σ.toRingHom) hmul
    rwa [Polynomial.map_map, hcomp, Polynomial.map_id, Polynomial.map_mul] at hh
  · rw [Polynomial.map_map, hσ', hχ, ← Polynomial.map_map, ← hfres, Polynomial.map_map, hid,
      Polynomial.map_id]
  · rw [Polynomial.map_map, hσ', hχ, ← Polynomial.map_map, ← hgres, Polynomial.map_map, hid,
      Polynomial.map_id]

end HenselianLocalRing
