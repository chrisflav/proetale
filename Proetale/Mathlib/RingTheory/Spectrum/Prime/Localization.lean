import Mathlib

/-!
# Testing equality of ring elements on localizations at primes

An element of a commutative ring is determined by its images in all localizations at
prime ideals. This is a direct consequence of
`PrimeSpectrum.toPiLocalization_injective`.
-/

namespace PrimeSpectrum

/-- Two elements of a commutative ring agreeing in every localization at a prime are
equal. -/
theorem eq_of_localizationAtPrime_eq {R : Type*} [CommRing R] {x y : R}
    (h : ∀ p : PrimeSpectrum R,
      algebraMap R (Localization.AtPrime p.asIdeal) x =
        algebraMap R (Localization.AtPrime p.asIdeal) y) : x = y :=
  PrimeSpectrum.toPiLocalization_injective R <| funext fun p ↦ h p

end PrimeSpectrum
