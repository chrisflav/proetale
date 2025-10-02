import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat

open CategoryTheory

namespace AlgebraicGeometry

-- This exists in Pi1 and is being upstreamed to mathlib.
instance {X Y : Scheme} (f : X ⟶ Y) [IsEtale f] : Flat f :=
  sorry

end AlgebraicGeometry
