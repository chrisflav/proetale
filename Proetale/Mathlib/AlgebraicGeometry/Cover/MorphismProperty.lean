import Mathlib.AlgebraicGeometry.Cover.MorphismProperty

universe v u

open CategoryTheory

namespace AlgebraicGeometry

variable {P : MorphismProperty Scheme.{u}} {S : Scheme.{u}}

attribute [ext] Scheme.Cover.Hom

@[simps toPreZeroHypercover]
abbrev Scheme.Cover.weaken {Q : MorphismProperty Scheme.{u}} (hPQ : P ≤ Q)
    (𝒰 : Cover.{v} (precoverage P) S) :
    S.Cover (precoverage Q) where
  __ := 𝒰
  mem₀ := by
    rw [ofArrows_mem_precoverage_iff]
    refine ⟨?_, ?_⟩
    · intro x
      exact 𝒰.exists_eq x
    · intro i
      apply hPQ
      exact 𝒰.map_prop i

end AlgebraicGeometry
