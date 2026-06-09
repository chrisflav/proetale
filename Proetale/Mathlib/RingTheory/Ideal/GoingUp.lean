/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Integral ring maps of local rings are local

If `R → S` is an integral ring map of local rings, then `R → S` is automatically a
local ring homomorphism. Unlike `RingHom.IsIntegral.isLocalHom`, this version does
not assume that `f` is injective.
-/

/-- An integral ring homomorphism between local rings is a local ring homomorphism.

Note that, unlike `RingHom.IsIntegral.isLocalHom`, this does not require injectivity of `f`. -/
theorem RingHom.IsIntegral.isLocalHom_of_isLocalRing
    {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    {f : R →+* S} (hf : f.IsIntegral) :
    IsLocalHom f :=
  ((IsLocalRing.local_hom_TFAE f).out 0 4).mpr <|
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf _)

/-- The structure map of an integral algebra between local rings is a local ring homomorphism.

Note that, unlike `Algebra.IsIntegral.isLocalHom`, this does not require `FaithfulSMul R S`.
This is intentionally not registered as an instance: the analogous Mathlib instance
`Algebra.IsIntegral.isLocalHom` is already known to cause typeclass search performance issues
(see `attribute [-instance]` in `Mathlib/RingTheory/QuasiFinite/Basic.lean`). -/
theorem Algebra.IsIntegral.isLocalHom_of_isLocalRing
    {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [Algebra.IsIntegral R S] :
    IsLocalHom (algebraMap R S) :=
  RingHom.IsIntegral.isLocalHom_of_isLocalRing Algebra.IsIntegral.isIntegral
