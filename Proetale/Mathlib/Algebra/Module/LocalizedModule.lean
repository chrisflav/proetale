/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Uniform annihilation of finitely generated modules with subsingleton localization

If `M` is a finitely generated `R`-module and `T ⊆ R` is a submonoid such that the
localized module `T⁻¹ M` is trivial, then there is a single element `t ∈ T` whose
action annihilates all of `M`.

This is the "uniform" version of `LocalizedModule.subsingleton_iff` for finitely
generated modules.
-/

variable {R : Type*} [CommRing R] {M : Type*} [AddCommMonoid M] [Module R M]

/-- If `M` is a finitely generated `R`-module, `T ⊆ R` is a submonoid, and the
localized module `T⁻¹ M` is subsingleton, then there is a single element `t ∈ T`
whose action annihilates all of `M`. -/
lemma Module.Finite.exists_mem_smul_eq_zero_of_subsingleton_localizedModule
    [Module.Finite R M] (T : Submonoid R) [Subsingleton (LocalizedModule T M)] :
    ∃ t ∈ T, ∀ m : M, t • m = 0 := by
  classical
  obtain ⟨s, hs⟩ := ‹Module.Finite R M›
  have hzero : ∀ m : M, ∃ r ∈ T, r • m = 0 :=
    (LocalizedModule.subsingleton_iff (S := T) (R := R) (M := M)).mp inferInstance
  choose t ht ht' using fun x : s ↦ hzero (x : M)
  refine ⟨s.attach.prod t, T.prod_mem (fun x _ ↦ ht x), fun m ↦ ?_⟩
  have hm : m ∈ Submodule.span R (s : Set M) := hs ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem t (Finset.mem_attach _ ⟨x, hx⟩)
    rw [hc, mul_comm, mul_smul, ht', smul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_comm, hx, smul_zero]
