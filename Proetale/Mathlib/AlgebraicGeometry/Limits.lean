import Mathlib.AlgebraicGeometry.Limits
import Upstreamer

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry

@[upstreamed mathlib 34014]
instance : HasFiniteCoproducts Scheme.{u} where
  out := inferInstance

@[upstreamed mathlib 34014]
instance : IsEmpty (⊥_ Scheme) := by
  rw [← isInitial_iff_isEmpty]
  exact ⟨initialIsInitial⟩

end AlgebraicGeometry
