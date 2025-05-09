import Mathlib.AlgebraicGeometry.Morphisms.Basic

universe u

open CategoryTheory

namespace AlgebraicGeometry

instance : IsLocalAtSource (⊤ : MorphismProperty Scheme.{u}) where
  iff_of_openCover' := by simp

instance : IsLocalAtTarget (⊤ : MorphismProperty Scheme.{u}) where
  iff_of_openCover' := by simp

end AlgebraicGeometry
