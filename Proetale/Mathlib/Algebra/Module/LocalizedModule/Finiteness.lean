/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Maps

/-!
# Uniform annihilation of finitely generated modules with subsingleton localization

If `M` is a finitely generated `R`-module and `g : M →ₗ[R] M'` realizes `M'` as the
localization of `M` at a submonoid `S ⊆ R`, then `M'` is trivial if and only if a
single element `t ∈ S` annihilates all of `M`. This strengthens
`IsLocalizedModule.subsingleton_iff` by providing a uniform witness independent of
the element.
-/

variable {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]

/-- If `N` is a finitely generated submodule of `M` and every element of `N` is
`S`-torsion, then a single element of `S` annihilates all of `N`. -/
lemma Submodule.FG.exists_mem_smul_eq_zero {N : Submodule R M}
    (hN : N.FG) (S : Submonoid R) (h : ∀ x ∈ N, ∃ t ∈ S, t • x = 0) :
    ∃ t ∈ S, ∀ x ∈ N, t • x = 0 := by
  classical
  obtain ⟨s, hs⟩ := hN
  choose t ht ht' using fun x : s ↦ h (x : M) (hs ▸ Submodule.subset_span x.2)
  refine ⟨∏ x ∈ s.attach, t x, S.prod_mem fun x _ ↦ ht x, fun m hm ↦ ?_⟩
  have hann : ∏ x ∈ s.attach, t x ∈ N.annihilator := by
    rw [← hs, Submodule.mem_annihilator_span]
    rintro ⟨x, hx⟩
    rw [← Finset.prod_erase_mul _ _ (s.mem_attach ⟨x, hx⟩), mul_smul, ht', smul_zero]
  exact Submodule.mem_annihilator.mp hann m hm

variable {M' : Type*} [AddCommMonoid M'] [Module R M']

namespace IsLocalizedModule

/-- If `M` is a finitely generated `R`-module whose localization `M'` at `S` is
trivial, then a single element of `S` annihilates all of `M`. -/
lemma exists_mem_smul_eq_zero_of_subsingleton
    [Module.Finite R M] (S : Submonoid R) (g : M →ₗ[R] M')
    [IsLocalizedModule S g] [Subsingleton M'] :
    ∃ t ∈ S, ∀ m : M, t • m = 0 := by
  obtain ⟨t, htS, ht⟩ := Module.Finite.fg_top.exists_mem_smul_eq_zero S
    fun x _ ↦ (IsLocalizedModule.subsingleton_iff S g).mp inferInstance x
  exact ⟨t, htS, fun m ↦ ht m Submodule.mem_top⟩

/-- For a finitely generated `R`-module `M` and a localization `g : M →ₗ[R] M'`
of `M` at a submonoid `S ⊆ R`, `M'` is trivial iff a single element of `S`
annihilates all of `M`. -/
lemma subsingleton_iff_exists_mem_smul_eq_zero
    [Module.Finite R M] (S : Submonoid R) (g : M →ₗ[R] M') [IsLocalizedModule S g] :
    Subsingleton M' ↔ ∃ t ∈ S, ∀ m : M, t • m = 0 := by
  refine ⟨?_, ?_⟩
  · intro
    exact exists_mem_smul_eq_zero_of_subsingleton S g
  · rintro ⟨t, htS, ht⟩
    exact (IsLocalizedModule.subsingleton_iff S g).mpr fun m ↦ ⟨t, htS, ht m⟩

end IsLocalizedModule
