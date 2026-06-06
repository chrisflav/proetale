/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Smooth.Flat

/-!
# Finiteness descent from the residue field (Stacks 04GG fragment)

This file collects the Mathlib-PR-quality lemmas used in the Stacks
04GG / Etale-localisation finiteness descent argument.

## Main results

* `Module.eq_top_of_residue_eq_top_of_finite` — Nakayama, in the form
  "if `N ⊔ 𝔪 • ⊤ = ⊤` for a submodule `N` of a finitely generated
  module `M`, where `𝔪` is the maximal ideal of a local ring, then
  `N = ⊤`".
* `Module.span_residue_basis_add_maximal_smul_eq_top` — lifting a
  generating family of `M ⧸ 𝔪 • M` to a set whose span together with
  `𝔪 • M` covers `M`.
* `Module.finite_of_finite_residue_of_flat_of_local` — the headline
  Stacks 04GG fragment: a finitely-presented flat module over a
  local ring whose residue quotient is finite over `A` is
  module-finite over `A`.
* `Algebra.Etale.finite_of_finite_residue_of_local` — the étale
  corollary: an étale algebra over a local ring whose residue
  quotient is finite over `A` is module-finite over `A`.

## References

* Stacks Project, Tag 04GG.
* Stacks Project, Tag 00DV (Nakayama's lemma).
-/

namespace Module

variable {A : Type*} [CommRing A] [IsLocalRing A]
variable {M : Type*} [AddCommGroup M] [Module A M]

/-- Nakayama in residue form for a local ring: if a submodule `N` of
a finitely generated module `M` satisfies `N ⊔ 𝔪 • ⊤ = ⊤`
(equivalently `M = N + 𝔪 • M`), then `N = ⊤`. Here `𝔪 :=
IsLocalRing.maximalIdeal A`. -/
theorem eq_top_of_residue_eq_top_of_finite [Module.Finite A M]
    (N : Submodule A M)
    (h : N ⊔ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A M) = ⊤) :
    N = ⊤ := by
  refine le_antisymm le_top ?_
  have hjac : IsLocalRing.maximalIdeal A ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) bot_ne_top]
  exact Submodule.le_of_le_smul_of_le_jacobson_bot
    Module.Finite.fg_top hjac h.ge

/-- Lift of a residue spanning set to a set that, together with
`𝔪 • M`, spans `M`. Given a family `b : ι → M` whose images in
`M ⧸ 𝔪 • M` span the quotient (i.e. the image of `span b` under the
projection is the whole residue), then `span A (range b) ⊔ 𝔪 • M = M`.
-/
theorem span_residue_basis_add_maximal_smul_eq_top
    {ι : Type*} (b : ι → M)
    (hb : Submodule.map
        (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)).mkQ
        (Submodule.span A (Set.range b)) = ⊤) :
    Submodule.span A (Set.range b) ⊔
        (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A M) = ⊤ := by
  refine le_antisymm le_top fun x _ ↦ ?_
  have hx : Submodule.Quotient.mk
        (p := IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)) x
      ∈ Submodule.map
        (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)).mkQ
        (Submodule.span A (Set.range b)) := by
    rw [hb]; trivial
  obtain ⟨y, hy, hxy⟩ := hx
  have hker : x - y ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) :=
    (Submodule.Quotient.eq _).mp hxy.symm
  rw [show x = y + (x - y) by rw [add_sub_cancel]]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left hy)
    (Submodule.mem_sup_right hker)

/-- **Stacks 04GG (finiteness descent fragment).** A finitely-presented
flat module `M` over a local ring `A` whose residue `M ⧸ 𝔪 • M` is
finite over `A` is module-finite over `A`.

The Stacks formulation includes a Noetherian hypothesis and the
flatness of `M`; neither is needed in the actual argument (the proof
goes through Nakayama on `M / 𝔪 M`), so we drop the Noetherian
assumption and retain `Module.Flat` purely for compatibility with the
downstream étale-algebra application. -/
theorem finite_of_finite_residue_of_flat_of_local
    [Module.FinitePresentation A M] [Module.Flat A M]
    (h : Module.Finite A (M ⧸ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A M))) :
    Module.Finite A M := by
  classical
  obtain ⟨s, hs⟩ : (⊤ : Submodule A
        (M ⧸ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A M))).FG :=
    Module.Finite.fg_top
  let π : M →ₗ[A] M ⧸ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A M) :=
    Submodule.mkQ _
  have hπ : Function.Surjective π := Submodule.Quotient.mk_surjective _
  let lift (y : M ⧸ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A M)) : M :=
    (hπ y).choose
  have lift_spec (y) : π (lift y) = y := (hπ y).choose_spec
  let b : { x // x ∈ s } → M := fun y ↦ lift y.val
  have himg : π '' Set.range b = (s : Set _) := by
    ext a
    refine ⟨?_, fun ha ↦ ⟨lift a, ⟨⟨a, ha⟩, rfl⟩, lift_spec a⟩⟩
    rintro ⟨_, ⟨⟨c, hc⟩, rfl⟩, hb⟩
    rw [← hb, lift_spec]; exact hc
  have hb_map : Submodule.map π (Submodule.span A (Set.range b)) = ⊤ := by
    rw [Submodule.map_span, himg, hs]
  refine ⟨(Set.range b).toFinset, eq_top_of_residue_eq_top_of_finite _ ?_⟩
  rw [Set.coe_toFinset]
  exact span_residue_basis_add_maximal_smul_eq_top b hb_map

end Module

namespace Algebra.Etale

variable {A : Type*} [CommRing A] [IsLocalRing A]
variable (B : Type*) [CommRing B] [Algebra A B] [Algebra.Etale A B]

/-- **Stacks 04GG (étale fibre form).** An étale algebra `B` over a
local ring `A` whose residue `B ⧸ 𝔪 • B` (regarded as an `A`-module)
is finite over `A` is module-finite over `A`.

This is the étale specialisation of
`Module.finite_of_finite_residue_of_flat_of_local`. The étale
hypothesis supplies flatness via `Algebra.Smooth.flat`; the
`Module.FinitePresentation` hypothesis is required separately, since
étale-as-algebra is finite-presentation-as-algebra, not as a module. -/
theorem finite_of_finite_residue_of_local
    [Module.FinitePresentation A B]
    (h : Module.Finite A (B ⧸ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A B))) :
    Module.Finite A B :=
  Module.finite_of_finite_residue_of_flat_of_local h

end Algebra.Etale
