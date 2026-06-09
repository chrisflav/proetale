/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Quasi-compact covers of flat, locally finitely presented morphisms

This file packages the blueprint statement `lemma:qc-cover-of-flat-fp`:
a jointly surjective family of morphisms that are flat and locally of finite
presentation is a quasi-compact cover. The proof combines
`UniversallyOpen.of_flat` (Stacks 01UA) with `QuasiCompactCover.of_isOpenMap`
(Stacks 022C).
-/

universe v u

open CategoryTheory

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- A jointly surjective family of flat morphisms locally of finite presentation is
quasi-compact: each component is universally open, hence an open map, so
`QuasiCompactCover.of_isOpenMap` applies. -/
lemma QuasiCompactCover.of_flat_locallyOfFinitePresentation
    {K : Precoverage Scheme.{u}} (𝒰 : S.Cover K) [Scheme.JointlySurjective K]
    [∀ i, Flat (𝒰.f i)] [∀ i, LocallyOfFinitePresentation (𝒰.f i)] :
    QuasiCompactCover 𝒰.toPreZeroHypercover :=
  .of_isOpenMap fun _ ↦ (𝒰.f _).isOpenMap

end AlgebraicGeometry
