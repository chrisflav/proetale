/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Vanishing of Ext classes via resolutions

Let `Z` and `G` be objects of an abelian category `C` and let
`⋯ ⟶ T (n + 1) ⟶ T n ⟶ ⋯ ⟶ T 0 ⟶ Z ⟶ 0` be a resolution of `Z`, given by termwise data
`d : ∀ n, T (n + 1) ⟶ T n` and an augmentation `ε : T 0 ⟶ Z`.

We show the vanishing criterion `CategoryTheory.Abelian.Ext.eq_zero_of_resolution`:
a class `ξ : Ext Z G (m + 1)` vanishes provided that
* the restriction of `ξ` along `ε` vanishes;
* the groups `Ext (T n) G q` vanish for `0 < q < m + 1`; and
* every cocycle `φ : T (m + 1) ⟶ G` (i.e. `d (m + 1) ≫ φ = 0`) is a coboundary
  (i.e. of the form `d m ≫ ψ`).

This is the standard "hypercohomology via resolutions" computation in low degrees, expressed
with explicit cocycle conditions; it replaces the Čech-to-derived functor spectral sequence
argument in degrees `≤ m + 1`.
-/

universe w v u

namespace CategoryTheory.Abelian.Ext

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Let `⋯ ⟶ T (n + 1) ⟶ T n ⟶ ⋯ ⟶ T 0 ⟶ Z ⟶ 0` be a resolution of `Z`. Then a class
`ξ : Ext Z G (m + 1)` vanishes, if its restriction along the augmentation `ε : T 0 ⟶ Z`
vanishes, the groups `Ext (T n) G q` vanish for `0 < q < m + 1` and every cocycle
`φ : T (m + 1) ⟶ G` is a coboundary.

This computes hypercohomology in low degrees via a resolution and replaces the
Čech-to-derived functor spectral sequence argument in degrees `≤ m + 1`. -/
theorem eq_zero_of_resolution {Z G : C} (m : ℕ)
    (T : ℕ → C) (d : ∀ n, T (n + 1) ⟶ T n) (ε : T 0 ⟶ Z)
    (hdd : ∀ n, d (n + 1) ≫ d n = 0) (hdε : d 0 ≫ ε = 0) (hε : Epi ε)
    (hex0 : (ShortComplex.mk (d 0) ε hdε).Exact)
    (hexs : ∀ n, (ShortComplex.mk (d (n + 1)) (d n) (hdd n)).Exact)
    (hT : ∀ (n q : ℕ), 0 < q → q < m + 1 → Subsingleton (Ext (T n) G q))
    (hcoc : ∀ (φ : T (m + 1) ⟶ G), d (m + 1) ≫ φ = 0 → ∃ ψ : T m ⟶ G, φ = d m ≫ ψ)
    (ξ : Ext Z G (m + 1))
    (hξ : (mk₀ ε).comp ξ (zero_add (m + 1)) = 0) :
    ξ = 0 := by
  induction m generalizing Z T d ε hdd hdε hε hex0 hexs with
  | zero =>
    -- The short exact sequence `0 ⟶ kernel ε ⟶ T 0 ⟶ Z ⟶ 0`.
    have hS : (ShortComplex.mk (kernel.ι ε) ε (kernel.condition ε)).ShortExact :=
      { exact := ShortComplex.exact_kernel ε, epi_g := hε }
    -- Since the restriction of `ξ` along `ε` vanishes, `ξ` is the image of a
    -- morphism `kernel ε ⟶ G` under the boundary map.
    obtain ⟨η, hη⟩ := contravariant_sequence_exact₃ hS G ξ hξ (n₀ := 0) rfl
    -- `d 0` induces an epimorphism `T 1 ↠ kernel ε` by exactness at `T 0`.
    have hd1 : d (0 + 1) ≫ kernel.lift ε (d 0) hdε = 0 := by
      rw [← cancel_mono (kernel.ι ε), Category.assoc, kernel.lift_ι, Limits.zero_comp]
      exact hdd 0
    have hπ : Epi (kernel.lift ε (d 0) hdε) := hex0.epi_kernelLift
    -- The composition `T 1 ↠ kernel ε ⟶ G` is a cocycle, hence a coboundary `d 0 ≫ ψ`.
    obtain ⟨ψ, hψ⟩ := hcoc (kernel.lift ε (d 0) hdε ≫ addEquiv₀ η) (by
      rw [← Category.assoc, hd1, Limits.zero_comp])
    -- Hence `η` factors through `T 0`, so its boundary `ξ` vanishes.
    have hσ : addEquiv₀ η = kernel.ι ε ≫ ψ := by
      rw [← cancel_epi (kernel.lift ε (d 0) hdε), hψ, ← Category.assoc, kernel.lift_ι]
    have hη' : η = mk₀ (kernel.ι ε ≫ ψ) := by
      rw [← hσ, mk₀_addEquiv₀_apply]
    rw [← hη, hη', ← mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc (mk₀ ψ)
  | succ m IH =>
    -- The short exact sequence `0 ⟶ kernel ε ⟶ T 0 ⟶ Z ⟶ 0`.
    have hS : (ShortComplex.mk (kernel.ι ε) ε (kernel.condition ε)).ShortExact :=
      { exact := ShortComplex.exact_kernel ε, epi_g := hε }
    -- Since the restriction of `ξ` along `ε` vanishes, `ξ` is the boundary of a
    -- class `η : Ext (kernel ε) G (m + 1)`.
    obtain ⟨η, hη⟩ := contravariant_sequence_exact₃ hS G ξ hξ (n₀ := m + 1) (by omega)
    -- The truncated complex `⋯ ⟶ T 2 ⟶ T 1 ⟶ kernel ε ⟶ 0` is a resolution of `kernel ε`.
    have hd1 : d (0 + 1) ≫ kernel.lift ε (d 0) hdε = 0 := by
      rw [← cancel_mono (kernel.ι ε), Category.assoc, kernel.lift_ι, Limits.zero_comp]
      exact hdd 0
    have hex0' : (ShortComplex.mk (d (0 + 1)) (kernel.lift ε (d 0) hdε) hd1).Exact :=
      (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
        (S₁ := ShortComplex.mk (d (0 + 1)) (kernel.lift ε (d 0) hdε) hd1)
        (S₂ := ShortComplex.mk (d (0 + 1)) (d 0) (hdd 0))
        { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι ε }).mpr (hexs 0)
    -- The restriction of `η` to `T 1` vanishes by the `Ext`-vanishing assumption, so the
    -- induction hypothesis applied to the truncated resolution shows `η = 0`.
    haveI : Subsingleton (Ext (T (0 + 1)) G (m + 1)) :=
      hT (0 + 1) (m + 1) (by omega) (by omega)
    have hη0 : η = 0 :=
      IH (fun n ↦ T (n + 1)) (fun n ↦ d (n + 1)) (kernel.lift ε (d 0) hdε)
        (fun n ↦ hdd (n + 1)) hd1 hex0.epi_kernelLift hex0' (fun n ↦ hexs (n + 1))
        (fun n q hq hq' ↦ hT (n + 1) q hq (by omega)) hcoc η (Subsingleton.elim _ 0)
    rw [← hη, hη0, comp_zero]

end CategoryTheory.Abelian.Ext
