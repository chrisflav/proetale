/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.RingTheory.Extension.Presentation.Core

/-!
# Stacks 00U3: FP-algebra descent along a filtered colimit of rings

If `F : J ⥤ CommRingCat` is a diagram over a filtered category with colimit cocone
`c` (so `c.pt = colim F`), and `φ : c.pt ⟶ A` is a finitely presented ring
homomorphism, then there exists a finite stage `j₀ : J` together with an FP
ring map `φⱼ : F.obj j₀ ⟶ Aⱼ` and a map `ψ : Aⱼ ⟶ A` such that the natural
square
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

/-- Given a finite set `s` of elements in the colimit, we can find a single stage
`j` of the filtered diagram together with a function lifting all elements of `s`
through `c.ι.app j`. -/
private lemma exists_finset_lift
    {J : Type u} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ CommRingCat.{u}} {c : Cocone F} (hc : IsColimit c)
    (s : Finset c.pt) :
    ∃ (j : J) (lift : c.pt → F.obj j),
      ∀ x ∈ s, (c.ι.app j).hom (lift x) = x := by
  classical
  have hForget : IsColimit ((forget CommRingCat.{u}).mapCocone c) :=
    isColimitOfPreserves (forget CommRingCat.{u}) hc
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
    exact ⟨j, fun _ => 0, by simp⟩
  | @insert a t ha ih =>
    obtain ⟨j₀, lift₀, h₀⟩ := ih
    obtain ⟨j₁, y₁, hy₁⟩ := Types.jointly_surjective_of_isColimit hForget a
    let j : J := IsFiltered.max j₀ j₁
    let m₀ : j₀ ⟶ j := IsFiltered.leftToMax j₀ j₁
    let m₁ : j₁ ⟶ j := IsFiltered.rightToMax j₀ j₁
    refine ⟨j, Function.update (fun x => (F.map m₀).hom (lift₀ x)) a
      ((F.map m₁).hom y₁), ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxt
    · rw [Function.update_self]
      have hw : F.map m₁ ≫ c.ι.app j = c.ι.app j₁ := c.w m₁
      have := congr($(hw).hom y₁)
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
      rw [this]
      exact hy₁
    · have hne : x ≠ a := fun heq => ha (heq ▸ hxt)
      rw [Function.update_of_ne hne]
      have hw : F.map m₀ ≫ c.ι.app j = c.ι.app j₀ := c.w m₀
      have := congr($(hw).hom (lift₀ x))
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
      rw [this]
      exact h₀ x hxt

/-- **Stacks 00U3**: FP-algebra descent along a filtered colimit of commutative rings.

If `F : J ⥤ CommRingCat` is a diagram over a filtered category with colimit cocone
`c` and `φ : c.pt ⟶ A` is a finitely presented ring map, then there exists a
finite stage `j₀ : J`, an object `Aⱼ` of `CommRingCat`, an FP map
`φⱼ : F.obj j₀ ⟶ Aⱼ`, and a map `ψ : Aⱼ ⟶ A`, such that the canonical
square `c.ι.app j₀ / φⱼ / φ / ψ` is a pushout (i.e. `A ≃ c.pt ⊗[F.obj j₀] Aⱼ`). -/
lemma exists_fp_algebra_descent_of_isColimit
    {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ CommRingCat.{u}}
    {c : Cocone F} (hc : IsColimit c)
    {A : CommRingCat.{u}} (φ : c.pt ⟶ A) (hφ : φ.hom.FinitePresentation) :
    ∃ (j₀ : J) (Aⱼ : CommRingCat.{u}) (φⱼ : F.obj j₀ ⟶ Aⱼ) (ψ : Aⱼ ⟶ A),
      φⱼ.hom.FinitePresentation ∧
      c.ι.app j₀ ≫ φ = φⱼ ≫ ψ ∧
      IsPushout (c.ι.app j₀) φⱼ φ ψ := by
  classical
  letI : Algebra c.pt A := φ.hom.toAlgebra
  haveI : Algebra.FinitePresentation c.pt A := hφ
  let n : ℕ := Algebra.Presentation.ofFinitePresentationVars (c.pt : Type u) (A : Type u)
  let m : ℕ := Algebra.Presentation.ofFinitePresentationRels (c.pt : Type u) (A : Type u)
  let P : Algebra.Presentation (c.pt : Type u) (A : Type u) (Fin n) (Fin m) :=
    Algebra.Presentation.ofFinitePresentation (c.pt : Type u) (A : Type u)
  have hPfin : P.coeffs.Finite := P.finite_coeffs
  obtain ⟨j₀, liftFun, hlift⟩ := exists_finset_lift hc hPfin.toFinset
  let R₀ : CommRingCat.{u} := F.obj j₀
  let ιR₀ : R₀ ⟶ c.pt := c.ι.app j₀
  letI : Algebra R₀ c.pt := ιR₀.hom.toAlgebra
  letI : Algebra R₀ A := (ιR₀ ≫ φ).hom.toAlgebra
  have algR₀R_eq : (algebraMap R₀ c.pt : R₀ →+* c.pt) = ιR₀.hom :=
    RingHom.algebraMap_toAlgebra ιR₀.hom
  have algR₀A_eq : (algebraMap R₀ A : R₀ →+* A) = (ιR₀ ≫ φ).hom :=
    RingHom.algebraMap_toAlgebra (ιR₀ ≫ φ).hom
  haveI : IsScalarTower R₀ c.pt A := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [algR₀R_eq, algR₀A_eq]
    change φ.hom (ιR₀.hom x) = (ιR₀ ≫ φ).hom x
    simp [CommRingCat.hom_comp]
  haveI : P.HasCoeffs R₀ := by
    refine ⟨fun r hr => ?_⟩
    have hr' : r ∈ hPfin.toFinset := hPfin.mem_toFinset.mpr hr
    refine ⟨liftFun r, ?_⟩
    have := hlift r hr'
    rw [algR₀R_eq]
    exact this
  let Aⱼcarrier : Type u := P.ModelOfHasCoeffs R₀
  let Aⱼ : CommRingCat.{u} := CommRingCat.of Aⱼcarrier
  haveI : Algebra.FinitePresentation R₀ Aⱼcarrier := inferInstance
  let φⱼ : R₀ ⟶ Aⱼ := CommRingCat.ofHom (algebraMap R₀ Aⱼcarrier)
  let eAlg : (c.pt : Type u) ⊗[(R₀ : Type u)] Aⱼcarrier ≃ₐ[(c.pt : Type u)] (A : Type u) :=
    P.tensorModelOfHasCoeffsEquiv R₀
  let ψ : Aⱼ ⟶ A :=
    CommRingCat.ofHom <|
      (eAlg.toAlgHom.toRingHom).comp
        (Algebra.TensorProduct.includeRight (R := R₀) (A := c.pt)
          (B := Aⱼcarrier)).toRingHom
  refine ⟨j₀, Aⱼ, φⱼ, ψ, ?fp, ?comm, ?pushout⟩
  · change (algebraMap R₀ Aⱼcarrier).FinitePresentation
    rw [RingHom.finitePresentation_algebraMap]
    infer_instance
  · ext x
    let f : Aⱼcarrier →ₐ[R₀] (A : Type u) :=
      (eAlg.restrictScalars R₀).toAlgHom.comp
        (Algebra.TensorProduct.includeRight (R := R₀) (A := c.pt) (B := Aⱼcarrier))
    have hf : (eAlg.toAlgHom.toRingHom).comp
      (Algebra.TensorProduct.includeRight (R := R₀) (A := c.pt)
        (B := Aⱼcarrier)).toRingHom = f.toRingHom := rfl
    change φ.hom (ιR₀.hom x) =
      ((eAlg.toAlgHom.toRingHom).comp _) (algebraMap R₀ Aⱼcarrier x)
    rw [hf]
    change φ.hom (ιR₀.hom x) = f (algebraMap R₀ Aⱼcarrier x)
    rw [f.commutes x, algR₀A_eq]
    simp [CommRingCat.hom_comp]
  · have hpush :
        IsPushout (CommRingCat.ofHom (algebraMap R₀ c.pt))
          (CommRingCat.ofHom (algebraMap (R₀ : Type u) Aⱼcarrier))
          (CommRingCat.ofHom (S := (c.pt : Type u) ⊗[(R₀ : Type u)] Aⱼcarrier)
            Algebra.TensorProduct.includeLeftRingHom)
          (CommRingCat.ofHom (S := (c.pt : Type u) ⊗[(R₀ : Type u)] Aⱼcarrier)
            (Algebra.TensorProduct.includeRight.toRingHom)) :=
      CommRingCat.isPushout_tensorProduct R₀ c.pt Aⱼcarrier
    let eIso : CommRingCat.of ((c.pt : Type u) ⊗[(R₀ : Type u)] Aⱼcarrier) ≅ A :=
      { hom := CommRingCat.ofHom eAlg.toAlgHom.toRingHom
        inv := CommRingCat.ofHom eAlg.symm.toAlgHom.toRingHom
        hom_inv_id := by
          apply CommRingCat.hom_ext
          apply RingHom.ext
          intro y
          exact eAlg.symm_apply_apply y
        inv_hom_id := by
          apply CommRingCat.hom_ext
          apply RingHom.ext
          intro y
          exact eAlg.apply_symm_apply y }
    refine hpush.of_iso (Iso.refl R₀) (Iso.refl c.pt) (Iso.refl Aⱼ) eIso ?_ ?_ ?_ ?_
    · simp only [Iso.refl_hom]
      change CommRingCat.ofHom (algebraMap R₀ c.pt) = ιR₀
      rw [algR₀R_eq]
      rfl
    · simp only [Iso.refl_hom]
      rfl
    · simp only [Iso.refl_hom]
      ext x
      change eAlg (Algebra.TensorProduct.includeLeftRingHom x) = φ.hom x
      have hx : (Algebra.TensorProduct.includeLeftRingHom x :
          (c.pt : Type u) ⊗[(R₀ : Type u)] Aⱼcarrier) =
          algebraMap (c.pt : Type u) _ x := by
        simp [Algebra.TensorProduct.includeLeftRingHom, Algebra.TensorProduct.algebraMap_apply]
      rw [hx, eAlg.commutes]
      rfl
    · simp only [Iso.refl_hom]
      rfl

end CommRingCat
