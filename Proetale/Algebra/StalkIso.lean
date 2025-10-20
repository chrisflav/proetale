/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.LocalIso
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Ring homomorphisms bijective on stalks

In this file we define the property of ring homomorphisms of being bijective on stalks.

A ring homomorphism `R →+* S` is bijective on stalks if `R_q →+* S_p` is bijective
for every pair of primes `q = f⁻¹(p)`. In the literature, also the term "`R →+* S` identifies
local rings" is used.
-/

/-- A ring homomorphism `R →+* S` is bijective on stalks if `R_q →+* S_p` is bijective
for every pair of primes `q = f⁻¹(p)`. -/
@[stacks 096E "(2)"]
def RingHom.BijectiveOnStalks {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  ∀ (p : Ideal S) [p.IsPrime],
    Function.Bijective (Localization.localRingHom (p.comap f) p f rfl)

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Local isomorphisms are bijective on stalks. -/
lemma RingHom.IsLocalIso.bijectiveOnStalks {f : R →+* S} (hf : f.IsLocalIso) :
    f.BijectiveOnStalks :=
  sorry

lemma RingHom.BijectiveOnStalks.bijective_of_bijective {f : R →+* S}
    (hf : f.BijectiveOnStalks) (hb : Function.Bijective f.specComap) :
    Function.Bijective f :=
  sorry
