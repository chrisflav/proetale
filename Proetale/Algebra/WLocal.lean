/-
Copyright (c) 2025 Jiang Jiedong, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiang Jiedong, Christian Merten
-/
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Proetale.Mathlib.RingTheory.Henselian
import Proetale.Topology.SpectralSpace.WLocal
import Proetale.Algebra.StalkIso

/-!
# w-local rings

In this file we define w-local rings. A ring is w-local if its prime spectrum is
a w-local topological space.
-/

/-- A ring is w-local if it has a w-local prime spectrum. -/
@[mk_iff]
class IsWLocalRing (R : Type*) [CommSemiring R] : Prop where
  wLocalSpace_primeSepectrum : WLocalSpace (PrimeSpectrum R)

variable {R S : Type*} [CommRing R] [CommRing S]

lemma IsWLocalRing.of_surjective {f : R →+* S} (hf : Function.Surjective f) [IsWLocalRing R] :
    IsWLocalRing S :=
  sorry

/-- A ring homomorphism is w-local if the induced map on spectra is w-local. -/
def RingHom.IsWLocal {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) : Prop :=
  IsWLocalMap (PrimeSpectrum.comap f)

lemma RingHom.isWLocal_iff_isMaximal_of_isMaximal (f : R →+* S) :
    IsWLocal f ↔ ∀ (m : Ideal S) [m.IsMaximal], (m.comap f).IsMaximal := by
  rw [IsWLocal, isWLocalMap_iff]
  refine ⟨fun ⟨_, h⟩ m hm ↦ ?_, ?_⟩
  · sorry
  · sorry

namespace RingHom.IsWLocal

/-- A w-local ring map between w-local rings that is bijective on stalks and
bijective on connected components is bijective. -/
lemma bijective_of_bijective [IsWLocalRing R] [IsWLocalRing S] {f : R →+* S} (hw : f.IsWLocal)
    (hs : f.BijectiveOnStalks)
    (hb : (PrimeSpectrum.comap f).continuous.connectedComponentsMap.Bijective) :
    Function.Bijective f :=
  sorry

end RingHom.IsWLocal

/-- A w-strictly-local ring is a w-local ring whose stalks at maximal ideals are strictly Henselian
local rings. -/
class IsWStrictlyLocalRing (R : Type*) [CommRing R] : Prop extends IsWLocalRing R where
  isStrictlyHenselianLocalRing_localization (m : Ideal R) [m.IsMaximal] :
    IsStrictlyHenselianLocalRing (Localization.AtPrime m)
