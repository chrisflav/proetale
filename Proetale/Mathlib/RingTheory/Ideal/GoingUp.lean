/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Integral ring maps of local rings are local

If `R → S` is an integral ring map of local rings, then `R → S` is automatically a
local ring homomorphism. This is `Ideal.IsMaximal.under` (going-up) packaged through
the local-hom TFAE, with no injectivity hypothesis (cf. Mathlib's
`RingHom.IsIntegral.isLocalHom`, which assumes injectivity).
-/

namespace RingHom

variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

/-- An integral ring homomorphism between local rings is a local ring homomorphism.

Note that, unlike `RingHom.IsIntegral.isLocalHom`, this does not require injectivity of `f`. -/
theorem IsIntegral.isLocalHom_of_isLocalRing {f : R →+* S} (hf : f.IsIntegral) :
    IsLocalHom f := by
  have h : IsLocalHom f ↔ (IsLocalRing.maximalIdeal S).comap f = IsLocalRing.maximalIdeal R :=
    (IsLocalRing.local_hom_TFAE f).out 0 4
  have hmax : ((IsLocalRing.maximalIdeal S).comap f).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf _
  exact h.mpr (IsLocalRing.eq_maximalIdeal hmax)

end RingHom

namespace Algebra

variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
  [Algebra R S]

/-- The structure map of an integral algebra between local rings is a local ring homomorphism.

Note that, unlike `Algebra.IsIntegral.isLocalHom`, this does not require `FaithfulSMul R S`. -/
theorem IsIntegral.isLocalHom_of_isLocalRing [Algebra.IsIntegral R S] :
    IsLocalHom (algebraMap R S) :=
  RingHom.IsIntegral.isLocalHom_of_isLocalRing Algebra.IsIntegral.isIntegral

end Algebra
