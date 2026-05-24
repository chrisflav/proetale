/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Basic-open refinement of an open-immersion cover of an affine scheme

This file provides a key technical lemma:
given an affine scheme `X` covered by a family of open immersions
`f i : Y i ⟶ X`, one can find a covering family of basic opens
`D(g k) ↪ X` such that each `D(g k)` factors through some `f (h k)`.

This is used in the small affine pro-étale site to refine arbitrary open-immersion
Zariski covers of an affine pro-étale object into basic-open refinements lying in
the image of the inclusion `AffineProEt ⥤ ProEt`.
-/

universe v u

open CategoryTheory

namespace AlgebraicGeometry

/-- Pointwise basic-open refinement of an open-immersion cover of an affine scheme.

Given an affine scheme `X` and an open-immersion family `f i : Y i ⟶ X` whose
ranges cover `X`, for each point `x : X` we extract `i x : ι` (a chart containing
`x`) and a global section `g x : Γ(X, ⊤)` whose basic open `D(g x)` contains `x`
and is contained in the range of `f (i x)`. -/
lemma exists_basicOpen_refinement_of_isAffine_cover
    {X : Scheme.{u}} [IsAffine X] {ι : Type v} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcov : ⋃ i, Set.range (f i).base = Set.univ) :
    ∃ (i : X → ι) (g : X → Γ(X, ⊤)),
      (∀ x : X, x ∈ X.basicOpen (g x)) ∧
      (∀ x : X, X.basicOpen (g x) ≤ (f (i x)).opensRange) := by
  classical
  -- Choose a chart index for each point.
  have hpt : ∀ x : X, ∃ i, x ∈ (f i).opensRange := fun x ↦ by
    have hx : x ∈ ⋃ i, Set.range (f i).base := by rw [hcov]; trivial
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hx
    exact ⟨i, hi⟩
  refine ⟨fun x ↦ (hpt x).choose, fun x ↦ ?_, fun x ↦ ?_, fun x ↦ ?_⟩
  · -- Pick a basic open containing `x` and contained in the chart `(f (i x)).opensRange`.
    have hxi : x ∈ (f (hpt x).choose).opensRange := (hpt x).choose_spec
    exact ((isAffineOpen_top X).exists_basicOpen_le
      (V := (f (hpt x).choose).opensRange) ⟨x, hxi⟩ trivial).choose
  · have hxi : x ∈ (f (hpt x).choose).opensRange := (hpt x).choose_spec
    exact ((isAffineOpen_top X).exists_basicOpen_le
      (V := (f (hpt x).choose).opensRange) ⟨x, hxi⟩ trivial).choose_spec.2
  · have hxi : x ∈ (f (hpt x).choose).opensRange := (hpt x).choose_spec
    exact ((isAffineOpen_top X).exists_basicOpen_le
      (V := (f (hpt x).choose).opensRange) ⟨x, hxi⟩ trivial).choose_spec.1

/-- Variant of `exists_basicOpen_refinement_of_isAffine_cover` packaging the basic
opens as `Scheme` morphisms factoring through the cover. For each point `x : X`,
returns:
- the chart index `i x : ι`,
- the global section `g x : Γ(X, ⊤)`,
- the lift `e x : (X.basicOpen (g x) : Scheme) ⟶ Y (i x)`
satisfying `e x ≫ f (i x) = (X.basicOpen (g x)).ι`. The basic opens `D(g x)`
cover `X` (every point is in its own basic open). -/
lemma exists_basicOpen_lift_of_isAffine_cover
    {X : Scheme.{u}} [IsAffine X] {ι : Type v} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcov : ⋃ i, Set.range (f i).base = Set.univ) :
    ∃ (i : X → ι) (g : X → Γ(X, ⊤))
      (e : ∀ x, (X.basicOpen (g x) : Scheme) ⟶ Y (i x)),
      (∀ x : X, x ∈ X.basicOpen (g x)) ∧
      (∀ x : X, e x ≫ f (i x) = (X.basicOpen (g x)).ι) := by
  obtain ⟨i, g, hmem, hle⟩ :=
    exists_basicOpen_refinement_of_isAffine_cover f hcov
  -- Lift each `(X.basicOpen (g x)).ι` through the open immersion `f (i x)`.
  refine ⟨i, g, fun x ↦ ?_, hmem, fun x ↦ ?_⟩
  · refine IsOpenImmersion.lift (f (i x)) (X.basicOpen (g x)).ι ?_
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange]
    exact_mod_cast hle x
  · refine IsOpenImmersion.lift_fac (f (i x)) (X.basicOpen (g x)).ι ?_

/-- The basic opens `D(g x)` produced by `exists_basicOpen_refinement_of_isAffine_cover`
cover `X` (as a set of points). -/
lemma iUnion_basicOpen_eq_univ_of_pointwise_mem
    {X : Scheme.{u}} {g : X → Γ(X, ⊤)} (hmem : ∀ x : X, x ∈ X.basicOpen (g x)) :
    ⋃ x : X, (X.basicOpen (g x)).carrier = Set.univ := by
  refine Set.eq_univ_of_forall (fun x ↦ ?_)
  exact Set.mem_iUnion.mpr ⟨x, hmem x⟩

end AlgebraicGeometry
