import Mathlib.AlgebraicGeometry.Cover.MorphismProperty

universe v u

open CategoryTheory

namespace AlgebraicGeometry

variable {P : MorphismProperty Scheme.{u}} {S : Scheme.{u}}

attribute [ext] Scheme.Cover.Hom

@[simps]
abbrev Scheme.Cover.weaken {Q : MorphismProperty Scheme.{u}} (hPQ : P ≤ Q) (𝒰 : Cover.{v} P S) :
    S.Cover Q where
  __ := 𝒰
  map_prop j := hPQ _ (𝒰.map_prop j)

end AlgebraicGeometry
