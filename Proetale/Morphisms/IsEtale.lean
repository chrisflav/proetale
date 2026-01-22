import Mathlib

universe u

open CategoryTheory Limits MorphismProperty Algebra

namespace AlgebraicGeometry

theorem IsEtale.of_flat_of_locallyOfFinitePresentation_of_formallyUnramified {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] [FormallyUnramified f] : IsEtale f := by
  sorry

end AlgebraicGeometry
