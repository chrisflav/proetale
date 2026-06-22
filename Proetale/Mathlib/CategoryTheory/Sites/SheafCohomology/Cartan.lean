/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.Algebra.Homology.DerivedCategory.Ext.Resolution
import Proetale.Mathlib.CategoryTheory.Sites.SheafCohomology.CechResolution
import Proetale.Mathlib.CategoryTheory.Sites.SheafCohomology.LocallyVanish

/-!
# Cartan's vanishing criterion

Let `(C, J)` be a site and `F` an abelian sheaf on it. Suppose that `P` is a collection of
objects of `C` such that every covering sieve of an object satisfying `P` contains a
singleton cover `f : V ⟶ U` which itself generates a covering sieve, whose Čech nerve
consists of objects satisfying `P`, and for which the Čech complex of `F` is exact in
positive degrees. Then the cohomology of `F` vanishes in positive degrees on every object
satisfying `P`.

This is a variant of [SGA 4, V.4.3]; the classical Čech-to-derived functor spectral
sequence is replaced by the elementary dimension-shifting lemma
`CategoryTheory.Abelian.Ext.eq_zero_of_resolution`.
-/

universe w u

open CategoryTheory Limits Opposite Abelian

namespace CategoryTheory

open scoped Simplicial

variable {C : Type (u + 1)} [Category.{u} C] [HasFiniteWidePullbacks C]
variable {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u + 1}]
variable [J.HasSheafCompose (forget AddCommGrpCat.{u + 1})]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{u + 1})]
variable [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]

/-- **Cartan's vanishing criterion.** Let `P` be a collection of objects of a site such that
for every covering sieve `R` of a `P`-object `U` there is a morphism `f : V ⟶ U` which
generates a covering sieve, whose Čech nerve consists of `P`-objects, for which every
positive-degree Čech cocycle of `F` is a coboundary, and such that every `Ext`-class on `U`
that vanishes on `R` also vanishes when restricted along `f` (e.g. because `f` refines a
finite disjoint subcover contained in `R`). Then `Ext^q(ℤ[U], F)` vanishes for all `q > 0`
and all `P`-objects `U`. -/
theorem Sheaf.ext_free_eq_zero_of_cech (P : C → Prop) (F : Sheaf J AddCommGrpCat.{u + 1})
    (hP : ∀ ⦃U : C⦄, P U → ∀ R ∈ J U, ∃ (V : C) (f : V ⟶ U),
      Sieve.generate (Presieve.singleton f) ∈ J U ∧
      (∀ n : ℕ, P ((Arrow.mk f).cechNerve.obj (op ⦋n⦌))) ∧
      (∀ (m : ℕ) (φ : cechFree J f (m + 1) ⟶ F), cechFreeD J f (m + 1) ≫ φ = 0 →
        ∃ ψ : cechFree J f m ⟶ F, φ = cechFreeD J f m ≫ ψ) ∧
      (∀ (q : ℕ) (ξ : Ext ((freeAbelianSheafFunctor J).obj U) F (q + 1)),
        (∀ ⦃W : C⦄ (g : W ⟶ U), R.arrows g →
          (Ext.mk₀ ((freeAbelianSheafFunctor J).map g)).comp ξ (zero_add (q + 1)) = 0) →
        (Ext.mk₀ ((freeAbelianSheafFunctor J).map f)).comp ξ (zero_add (q + 1)) = 0)) :
    ∀ (p : ℕ) ⦃U : C⦄, P U → ∀ ξ : Ext ((freeAbelianSheafFunctor J).obj U) F (p + 1), ξ = 0 := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p IH =>
    intro U hU ξ
    obtain ⟨R, hR, hξR⟩ := Sheaf.exists_mem_ext_map_eq_zero F p ξ
    obtain ⟨V, f, hfcov, hPnerve, hcoc, hkill⟩ := hP hU R hR
    refine Ext.eq_zero_of_resolution p (fun n ↦ cechFree J f n) (cechFreeD J f)
      (cechFreeAug J f) (cechFreeD_comp_d J f) (cechFreeD_comp_aug J f)
      (epi_cechFreeAug J f hfcov) (cechFree_exact_zero J f hfcov)
      (cechFree_exact_succ J f hfcov) (fun n q hq hqp ↦ ?_) (hcoc p) ξ ?_
    · -- vanishing of lower-degree cohomology of the Čech nerve objects, by induction
      obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt hq
      rw [zero_add]
      exact subsingleton_of_forall_eq 0 fun ξ' ↦ IH q (by omega) (hPnerve n) ξ'
    · -- the restriction along the augmentation vanishes
      have hf : (Ext.mk₀ ((freeAbelianSheafFunctor J).map f)).comp ξ (zero_add (p + 1)) = 0 :=
        hkill p ξ hξR
      have haug : (Arrow.mk f).augmentedCechNerve.hom.app (op ⦋0⦌) =
          WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 ≫ f :=
        (WidePullback.π_arrow _ _).symm
      calc (Ext.mk₀ (cechFreeAug J f)).comp ξ (zero_add (p + 1))
          = (Ext.mk₀ ((freeAbelianSheafFunctor J).map
              (WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) ≫
              (freeAbelianSheafFunctor J).map f)).comp ξ (zero_add (p + 1)) := by
            rw [cechFreeAug, haug, Functor.map_comp]
        _ = (Ext.mk₀ ((freeAbelianSheafFunctor J).map
              (WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0))).comp
              ((Ext.mk₀ ((freeAbelianSheafFunctor J).map f)).comp ξ (zero_add (p + 1)))
              (zero_add (p + 1)) := (Ext.mk₀_comp_mk₀_assoc _ _ _).symm
        _ = 0 := by rw [hf, Ext.comp_zero]

end CategoryTheory
