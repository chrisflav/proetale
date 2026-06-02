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
  {M' : Type*} [AddCommMonoid M'] [Module R M']

/-- Uniform-witness version of `IsLocalizedModule.subsingleton_iff` for finitely
generated modules: a single element of `S` works for all of `M`. -/
lemma Module.Finite.subsingleton_localizedModule_iff_exists_mem_smul_eq_zero
    [Module.Finite R M] (S : Submonoid R) (g : M →ₗ[R] M') [IsLocalizedModule S g] :
    Subsingleton M' ↔ ∃ t ∈ S, ∀ m : M, t • m = 0 := by
  refine ⟨fun _ ↦ ?_, fun ⟨t, htS, ht⟩ ↦
    (IsLocalizedModule.subsingleton_iff S g).mpr fun m ↦ ⟨t, htS, ht m⟩⟩
  classical
  obtain ⟨s, hs⟩ := ‹Module.Finite R M›.fg_top
  choose t ht ht' using fun x : s ↦
    (IsLocalizedModule.subsingleton_iff S g).mp ‹_› (x : M)
  refine ⟨s.attach.prod t, S.prod_mem fun x _ ↦ ht x, fun m ↦ ?_⟩
  have hann : s.attach.prod t ∈ (⊤ : Submodule R M).annihilator := by
    rw [← hs, Submodule.mem_annihilator_span]
    rintro ⟨x, hx⟩
    rw [← Finset.prod_erase_mul _ _ (s.mem_attach ⟨x, hx⟩), mul_smul, ht', smul_zero]
  exact Submodule.mem_annihilator.mp hann m Submodule.mem_top

/-- Typeclass-friendly form of
`Module.Finite.subsingleton_localizedModule_iff_exists_mem_smul_eq_zero`: if the
localization `M'` of a finitely generated module is trivial, a single element of
`S` annihilates all of `M`. -/
lemma Module.Finite.exists_mem_smul_eq_zero_of_subsingleton_localizedModule
    [Module.Finite R M] (S : Submonoid R) (g : M →ₗ[R] M')
    [IsLocalizedModule S g] [Subsingleton M'] :
    ∃ t ∈ S, ∀ m : M, t • m = 0 :=
  (Module.Finite.subsingleton_localizedModule_iff_exists_mem_smul_eq_zero S g).mp
    inferInstance
