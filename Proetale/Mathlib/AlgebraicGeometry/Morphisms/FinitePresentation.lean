/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Proetale.Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-!
# The diagonal of a locally of finite presentation morphism

The diagonal of a morphism that is locally of finite presentation is itself locally of finite
presentation. We deduce this from a cancellation property between
`LocallyOfFinitePresentation` and `LocallyOfFiniteType`, which follows from the general
`HasRingHomProperty.hasOfPostcompProperty`.
-/

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

instance : MorphismProperty.HasOfPostcompProperty
    @LocallyOfFinitePresentation @LocallyOfFiniteType := by
  refine HasRingHomProperty.hasOfPostcompProperty (Q := @RingHom.FinitePresentation)
    @LocallyOfFiniteType
    (Q' := @RingHom.FiniteType)
    (fun _ _ hf hcomp ↦ RingHom.FinitePresentation.of_comp_finiteType _ hcomp hf)
    (fun hg ↦ HasRingHomProperty.appTop _ _ hg) ?_
  intros _ _ _ f _ g hg
  exact HasRingHomProperty.comp_of_isOpenImmersion _ f g hg

/-- The diagonal of a morphism locally of finite presentation is locally of finite presentation. -/
theorem diagonal_locallyOfFinitePresentation {X Y : Scheme} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] : LocallyOfFinitePresentation (pullback.diagonal f) :=
  have : LocallyOfFinitePresentation (pullback.diagonal f ≫ pullback.fst f f) := by
    simpa only [pullback.diagonal_fst f] using locallyOfFinitePresentation_of_isOpenImmersion (𝟙 X)
  MorphismProperty.of_postcomp (W' := @LocallyOfFiniteType) _
    (pullback.diagonal f) (pullback.fst f f) inferInstance this

end AlgebraicGeometry
