/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Uniform annihilation of finitely generated modules with subsingleton localization

If `M` is a finitely generated `R`-module and `g : M →ₗ[R] M'` realizes `M'` as the
localization of `M` at a submonoid `S ⊆ R`, then `M'` is trivial if and only if a
single element `t ∈ S` annihilates all of `M`. This strengthens
`IsLocalizedModule.subsingleton_iff` under the finite generation hypothesis.
-/

variable {R : Type*} [CommRing R] {M : Type*} [AddCommMonoid M] [Module R M]
  {M' : Type*} [AddCommMonoid M'] [Module R M']

/-- For a finitely generated `R`-module `M` and a localization `g : M →ₗ[R] M'` at a
submonoid `S ⊆ R`, the localized module `M'` is trivial iff a single element of `S`
annihilates all of `M`. -/
lemma Module.Finite.subsingleton_iff_exists_mem_smul_eq_zero
    [Module.Finite R M] (S : Submonoid R) (g : M →ₗ[R] M') [IsLocalizedModule S g] :
    Subsingleton M' ↔ ∃ t ∈ S, ∀ m : M, t • m = 0 := by
  refine ⟨fun _ ↦ ?_, fun ⟨t, htS, ht⟩ ↦
    (IsLocalizedModule.subsingleton_iff S g).mpr fun m ↦ ⟨t, htS, ht m⟩⟩
  classical
  obtain ⟨s, hs⟩ := ‹Module.Finite R M›
  have hzero : ∀ m : M, ∃ r ∈ S, r • m = 0 :=
    (IsLocalizedModule.subsingleton_iff S g).mp inferInstance
  choose t ht ht' using fun x : s ↦ hzero (x : M)
  refine ⟨s.attach.prod t, S.prod_mem (fun x _ ↦ ht x), fun m ↦ ?_⟩
  have hm : m ∈ Submodule.span R (s : Set M) := by rw [hs]; exact Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem t (s.mem_attach ⟨x, hx⟩)
    rw [hc, mul_comm, mul_smul, ht', smul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_comm, hx, smul_zero]

/-- For a finitely generated `R`-module `M` and a localization `g : M →ₗ[R] M'` at a
submonoid `S ⊆ R`, if `M'` is trivial then a single element of `S` annihilates all
of `M`. -/
lemma Module.Finite.exists_mem_smul_eq_zero_of_subsingleton
    [Module.Finite R M] (S : Submonoid R) (g : M →ₗ[R] M')
    [IsLocalizedModule S g] [Subsingleton M'] :
    ∃ t ∈ S, ∀ m : M, t • m = 0 :=
  (Module.Finite.subsingleton_iff_exists_mem_smul_eq_zero S g).mp inferInstance
