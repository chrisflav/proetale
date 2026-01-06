import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.RingHom.Smooth

universe u

open CategoryTheory

lemma RingHom.Smooth.flat {R S : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : f.Smooth) :
    f.Flat :=
  sorry

namespace AlgebraicGeometry

-- This exists in Pi1 and is being upstreamed to mathlib.
instance {X Y : Scheme} (f : X ⟶ Y) [IsEtale f] : Flat f :=
  sorry

end AlgebraicGeometry
