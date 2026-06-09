/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Basic-open refinement of an open-immersion cover of an affine scheme

Given an affine scheme `X` covered by a family of open immersions `f i : Y i ⟶ X`,
this file produces a pointwise refinement by basic opens of `X`: for every `x : X`
there is an index `i x` and a global section `g x : Γ(X, ⊤)` such that
`x ∈ D(g x)` and `D(g x)` factors through `f (i x)`.

This is the key geometric input for showing that the inclusion
`AffineProEt ⥤ ProEt` is locally cover-dense for the Zariski topology.
-/

universe v u

open CategoryTheory

namespace AlgebraicGeometry

/-- Pointwise basic-open refinement of an open-immersion cover of an affine scheme.

Given an affine scheme `X` and an open-immersion family `f i : Y i ⟶ X` whose
ranges cover `X`, for each point `x : X` we extract an index `i x : ι` (a chart
containing `x`) and a global section `g x : Γ(X, ⊤)` whose basic open `D(g x)`
contains `x` and is contained in the range of `f (i x)`. -/
lemma exists_basicOpen_refinement_of_isAffine_cover
    {X : Scheme.{u}} [IsAffine X] {ι : Type v} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcov : ⋃ i, Set.range (f i).base = Set.univ) :
    ∃ (i : X → ι) (g : X → Γ(X, ⊤)),
      (∀ x : X, x ∈ X.basicOpen (g x)) ∧
      (∀ x : X, X.basicOpen (g x) ≤ (f (i x)).opensRange) := by
  classical
  have hpt : ∀ x : X, ∃ i, x ∈ (f i).opensRange := fun x => by
    have hx : x ∈ ⋃ i, Set.range (f i).base := by rw [hcov]; trivial
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hx
    exact ⟨i, hi⟩
  refine ⟨fun x => (hpt x).choose, fun x => ?_, fun x => ?_, fun x => ?_⟩
  all_goals
    have hxi : x ∈ (f (hpt x).choose).opensRange := (hpt x).choose_spec
    have h := ((isAffineOpen_top X).exists_basicOpen_le
      (V := (f (hpt x).choose).opensRange) ⟨x, hxi⟩ trivial).choose_spec
  · exact ((isAffineOpen_top X).exists_basicOpen_le
      (V := (f (hpt x).choose).opensRange) ⟨x, hxi⟩ trivial).choose
  · exact h.2
  · exact h.1

/-- Variant of `exists_basicOpen_refinement_of_isAffine_cover` packaging the basic
opens as `Scheme` morphisms factoring through the cover: for each `x : X` we
get a lift `e x : D(g x) ⟶ Y (i x)` satisfying `e x ≫ f (i x) = (D(g x)).ι`. -/
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
  refine ⟨i, g, fun x => ?_, hmem, fun x => ?_⟩
  · refine IsOpenImmersion.lift (f (i x)) (X.basicOpen (g x)).ι ?_
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange]
    exact_mod_cast hle x
  · exact IsOpenImmersion.lift_fac (f (i x)) (X.basicOpen (g x)).ι _

end AlgebraicGeometry
