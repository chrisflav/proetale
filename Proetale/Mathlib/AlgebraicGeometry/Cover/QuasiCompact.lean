/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Quasi-compact covers of flat, locally finitely presented morphisms

-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- A jointly surjective family of universally open morphisms is a quasi-compact cover. -/
@[stacks 022C]
instance QuasiCompactCover.of_universallyOpen
    {K : Precoverage Scheme.{u}} (𝒰 : S.Cover K) [Scheme.JointlySurjective K]
    [∀ i, UniversallyOpen (𝒰.f i)] :
    QuasiCompactCover 𝒰.toPreZeroHypercover :=
  .of_isOpenMap fun i ↦ (𝒰.f i).isOpenMap

/-- A jointly surjective family of flat morphisms locally of finite presentation is
quasi-compact. -/
@[stacks 01UA]
lemma QuasiCompactCover.of_flat_locallyOfFinitePresentation
    {K : Precoverage Scheme.{u}} (𝒰 : S.Cover K) [Scheme.JointlySurjective K]
    [∀ i, Flat (𝒰.f i)] [∀ i, LocallyOfFinitePresentation (𝒰.f i)] :
    QuasiCompactCover 𝒰.toPreZeroHypercover :=
  inferInstance

end AlgebraicGeometry
