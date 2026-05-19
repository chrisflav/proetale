import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.RingHom.Smooth

universe u

open CategoryTheory

namespace AlgebraicGeometry

-- This exists in Pi1 and is being upstreamed to mathlib.
instance {X Y : Scheme} (f : X ⟶ Y) [Etale f] : Flat f :=
  inferInstance

end AlgebraicGeometry
