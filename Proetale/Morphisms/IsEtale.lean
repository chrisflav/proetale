import Mathlib

universe u

open CategoryTheory Limits MorphismProperty Algebra

theorem xcsniubncv {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    [FinitePresentation R S] [FormallyUnramified R S] :
    IsStandardSmoothOfRelativeDimension 0 R S := by
  sorry

namespace AlgebraicGeometry

theorem IsEtale.of_flat_of_locallyOfFinitePresentation_of_formallyUnramified {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] [FormallyUnramified f] : IsEtale f := by
  sorry

end AlgebraicGeometry
