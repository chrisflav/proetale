/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.Extension.Presentation.Core

/-!
# Stacks 00U3: finitely presented algebra descent along a filtered colimit of rings

If `F : J ⥤ CommRingCat` is a diagram over a filtered category with colimit cocone
`c` (so `c.pt = colim F`), and `φ : c.pt ⟶ A` is a finitely presented ring
homomorphism, then there exists a finite stage `j₀ : J` together with a finitely
presented ring map `φⱼ : F.obj j₀ ⟶ Aⱼ` and a map `ψ : Aⱼ ⟶ A` such that the
natural square
```
F.obj j₀ ──── c.ι.app j₀ ────▶ c.pt
   │                              │
   φⱼ                             φ
   ▼                              ▼
   Aⱼ ─────────── ψ ────────────▶ A
```
is a pushout. In algebra-speak: `A ≃ c.pt ⊗[F.obj j₀] Aⱼ`.

This is Stacks Tag 00U3, the central ingredient for descending finitely presented
algebras along a filtered colimit of base rings.
-/

universe u

open CategoryTheory Limits TensorProduct

namespace CommRingCat

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **Stacks 00U3**: descent of a finitely presented algebra along a filtered colimit of
commutative rings.

If `F : J ⥤ CommRingCat` is a diagram over a filtered category with colimit cocone
`c` and `φ : c.pt ⟶ A` is a finitely presented ring map, then there exists a
finite stage `j₀ : J`, an object `Aⱼ` of `CommRingCat`, a finitely presented map
`φⱼ : F.obj j₀ ⟶ Aⱼ`, and a map `ψ : Aⱼ ⟶ A`, such that the canonical
square `c.ι.app j₀ / φⱼ / φ / ψ` is a pushout (i.e. `A ≃ c.pt ⊗[F.obj j₀] Aⱼ`). -/
@[stacks 00U3]
lemma exists_finitePresentation_descent_of_isColimit
    {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ CommRingCat.{u}}
    {c : Cocone F} (hc : IsColimit c)
    {A : CommRingCat.{u}} (φ : c.pt ⟶ A) (hφ : φ.hom.FinitePresentation) :
    ∃ (j₀ : J) (Aⱼ : CommRingCat.{u}) (φⱼ : F.obj j₀ ⟶ Aⱼ) (ψ : Aⱼ ⟶ A),
      φⱼ.hom.FinitePresentation ∧ IsPushout (c.ι.app j₀) φⱼ φ ψ := by
  classical
  letI : Algebra c.pt A := φ.hom.toAlgebra
  haveI : Algebra.FinitePresentation c.pt A := hφ
  -- Take an arbitrary finite presentation of `A` as a `c.pt`-algebra.
  let n : ℕ := Algebra.Presentation.ofFinitePresentationVars (c.pt : Type u) (A : Type u)
  let m : ℕ := Algebra.Presentation.ofFinitePresentationRels (c.pt : Type u) (A : Type u)
  let P : Algebra.Presentation (c.pt : Type u) (A : Type u) (Fin n) (Fin m) :=
    Algebra.Presentation.ofFinitePresentation _ _
  -- (a) Lift the finitely many coefficients of `P` to a common finite stage `j₀`.
  have hPfin : P.coeffs.Finite := P.finite_coeffs
  obtain ⟨j₀, liftFun, hlift⟩ := exists_lift_finset_of_isColimit hc hPfin.toFinset
  let R₀ : CommRingCat.{u} := F.obj j₀
  let ιR₀ : R₀ ⟶ c.pt := c.ι.app j₀
  letI : Algebra R₀ c.pt := ιR₀.hom.toAlgebra
  letI : Algebra R₀ A := (ιR₀ ≫ φ).hom.toAlgebra
  haveI : IsScalarTower R₀ c.pt A :=
    .of_algebraMap_eq fun x => by
      simp [RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp]
  haveI : P.HasCoeffs R₀ := by
    refine ⟨fun r hr => ⟨liftFun r, ?_⟩⟩
    rw [RingHom.algebraMap_toAlgebra]
    exact hlift r (hPfin.mem_toFinset.mpr hr)
  -- (b) Build the descended algebra `Aⱼ := P.ModelOfHasCoeffs R₀` and the descended map.
  let Aⱼ : CommRingCat.{u} := CommRingCat.of (P.ModelOfHasCoeffs R₀)
  let φⱼ : R₀ ⟶ Aⱼ := CommRingCat.ofHom (algebraMap R₀ (P.ModelOfHasCoeffs R₀))
  let eAlg : (c.pt : Type u) ⊗[(R₀ : Type u)] P.ModelOfHasCoeffs R₀ ≃ₐ[(c.pt : Type u)]
      (A : Type u) := P.tensorModelOfHasCoeffsEquiv R₀
  -- Equip `A` with an `Aⱼ`-algebra structure so that `ψ` and the pushout instance
  -- become definitional.
  let ψAlg : P.ModelOfHasCoeffs R₀ →ₐ[R₀] A :=
    (eAlg.restrictScalars R₀).toAlgHom.comp
      (Algebra.TensorProduct.includeRight (R := R₀) (A := c.pt) (B := P.ModelOfHasCoeffs R₀))
  letI : Algebra (P.ModelOfHasCoeffs R₀) A := ψAlg.toRingHom.toAlgebra
  haveI : IsScalarTower R₀ (P.ModelOfHasCoeffs R₀) A :=
    .of_algebraMap_eq fun r => (ψAlg.commutes r).symm
  let ψ : Aⱼ ⟶ A := CommRingCat.ofHom (algebraMap (P.ModelOfHasCoeffs R₀) A)
  refine ⟨j₀, Aⱼ, φⱼ, ψ, ?_, ?_⟩
  · -- `φⱼ` is the structure morphism of a finitely presented `R₀`-algebra.
    change (algebraMap R₀ (P.ModelOfHasCoeffs R₀)).FinitePresentation
    rw [RingHom.finitePresentation_algebraMap]
    infer_instance
  · -- (c) Conclude the pushout statement.
    haveI : Algebra.IsPushout R₀ c.pt (P.ModelOfHasCoeffs R₀) A :=
      Algebra.IsPushout.of_equiv (R := (R₀ : Type u)) (R' := (c.pt : Type u))
        (S := P.ModelOfHasCoeffs R₀) (S' := (c.pt : Type u) ⊗[(R₀ : Type u)] P.ModelOfHasCoeffs R₀)
        eAlg <| RingHom.ext fun x => by
          change eAlg (1 ⊗ₜ[R₀] x) = ψAlg x
          rfl
    exact CommRingCat.isPushout_of_isPushout R₀ c.pt (P.ModelOfHasCoeffs R₀) A

end CommRingCat
