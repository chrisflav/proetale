import Mathlib

/-!
# Membership in the maximal ideal along a local ring homomorphism

Small helper about `IsLocalHom`: for a local ring homomorphism between local rings,
membership in the maximal ideal can be tested after applying the map.
-/

namespace IsLocalRing

/-- For a local ring homomorphism `g : R →+* S` between local rings, an element `x`
lies in the maximal ideal of `R` if and only if `g x` lies in the maximal ideal of
`S`. -/
theorem map_mem_maximalIdeal_iff {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (g : R →+* S) [IsLocalHom g] (x : R) :
    g x ∈ maximalIdeal S ↔ x ∈ maximalIdeal R := by
  simp only [mem_maximalIdeal, mem_nonunits_iff, not_iff_not]
  exact isUnit_map_iff g x

end IsLocalRing
