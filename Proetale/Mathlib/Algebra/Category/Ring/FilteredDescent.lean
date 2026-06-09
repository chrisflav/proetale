/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.Algebra.Category.Ring.FilteredColimits
import Proetale.Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.Extension.Presentation.Core

/-!
# Stacks 00U3: finitely presented algebra descent along a filtered colimit of rings

This file proves the descent of finitely presented algebras along a filtered colimit of
commutative rings.

## Main results

* `CommRingCat.exists_finitePresentation_isPushout_of_isColimit`: if `c` is a filtered colimit
  cocone on `F : J ⥤ CommRingCat` and `φ : c.pt ⟶ A` is finitely presented, then `φ` descends
  to a finitely presented map at some stage `j₀`, fitting into a pushout square.

## References

* [Stacks: Tag 00U3](https://stacks.math.columbia.edu/tag/00U3)
-/

universe u

open CategoryTheory Limits TensorProduct

namespace CommRingCat

/-- **Stacks 00U3**: descent of a finitely presented algebra along a filtered colimit of
commutative rings. The conclusion exhibits the descended square
```
F.obj j₀ ──── c.ι.app j₀ ────▶ c.pt
   │                              │
   φⱼ                             φ
   ▼                              ▼
   Aⱼ ─────────── ψ ────────────▶ A
```
as a pushout. -/
@[stacks 00U3]
lemma exists_finitePresentation_isPushout_of_isColimit
    {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ CommRingCat.{u}}
    {c : Cocone F} (hc : IsColimit c)
    {A : CommRingCat.{u}} (φ : c.pt ⟶ A) (hφ : φ.hom.FinitePresentation) :
    ∃ (j₀ : J) (Aⱼ : CommRingCat.{u}) (φⱼ : F.obj j₀ ⟶ Aⱼ) (ψ : Aⱼ ⟶ A),
      φⱼ.hom.FinitePresentation ∧ IsPushout (c.ι.app j₀) φⱼ φ ψ := by
  classical
  let _ : Algebra c.pt A := φ.hom.toAlgebra
  have : Algebra.FinitePresentation c.pt A := hφ
  let P : Algebra.Presentation c.pt A _ _ := Algebra.Presentation.ofFinitePresentation _ _
  have hForget : IsColimit ((forget CommRingCat.{u}).mapCocone c) :=
    isColimitOfPreserves (forget CommRingCat.{u}) hc
  obtain ⟨j₀, lift, hlift⟩ :=
    Types.FilteredColimit.jointly_surjective_finset_of_isColimit hForget P.finite_coeffs.toFinset
  let R₀ : CommRingCat.{u} := F.obj j₀
  let _ : Algebra R₀ c.pt := (c.ι.app j₀).hom.toAlgebra
  let _ : Algebra R₀ A := (c.ι.app j₀ ≫ φ).hom.toAlgebra
  have : IsScalarTower R₀ c.pt A :=
    .of_algebraMap_eq fun _ ↦ by simp [RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp]
  have : P.HasCoeffs R₀ := by
    refine ⟨fun r hr ↦ ⟨lift ⟨r, P.finite_coeffs.mem_toFinset.mpr hr⟩, ?_⟩⟩
    rw [RingHom.algebraMap_toAlgebra]
    exact hlift ⟨r, P.finite_coeffs.mem_toFinset.mpr hr⟩
  let Aⱼ : CommRingCat.{u} := .of (P.ModelOfHasCoeffs R₀)
  let φⱼ : R₀ ⟶ Aⱼ := ofHom (algebraMap R₀ (P.ModelOfHasCoeffs R₀))
  let ψAlg : P.ModelOfHasCoeffs R₀ →ₐ[R₀] A :=
    ((P.tensorModelOfHasCoeffsHom R₀).restrictScalars R₀).comp Algebra.TensorProduct.includeRight
  let _ : Algebra (P.ModelOfHasCoeffs R₀) A := ψAlg.toAlgebra
  have : IsScalarTower R₀ (P.ModelOfHasCoeffs R₀) A :=
    .of_algebraMap_eq fun r ↦ (ψAlg.commutes r).symm
  refine ⟨j₀, Aⱼ, φⱼ, ofHom (algebraMap (P.ModelOfHasCoeffs R₀) A), ?_, ?_⟩
  · exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  · let _ := Algebra.TensorProduct.rightAlgebra (R := R₀) (A := c.pt) (B := P.ModelOfHasCoeffs R₀)
    have : Algebra.IsPushout R₀ c.pt (P.ModelOfHasCoeffs R₀) A :=
      Algebra.IsPushout.of_equiv (R := R₀) (R' := c.pt) (S := P.ModelOfHasCoeffs R₀)
        (S' := c.pt ⊗[R₀] P.ModelOfHasCoeffs R₀)
        (P.tensorModelOfHasCoeffsEquiv R₀) (RingHom.ext fun _ ↦ rfl)
    exact CommRingCat.isPushout_of_isPushout R₀ c.pt (P.ModelOfHasCoeffs R₀) A

end CommRingCat
